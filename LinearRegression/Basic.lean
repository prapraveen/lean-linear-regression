/-================================LIST UTILITY FUNCTIONS================================-/

def getColumn (a: Type) (lst2D : List (List a)) (idx : Nat) : List a :=
  /- Given a 2D list of data, returns the column given by the specified index.
     If the index is invalid for a row, that row is omitted from the output
  -/
  lst2D.filterMap (fun row => List.get? row idx)

#guard getColumn Nat [] 0 = []
#guard getColumn Nat [[]] 0 = []
#guard getColumn Nat [[1, 2, 3]] 2 = [3]
#guard getColumn Nat [[1, 2, 3], [4, 5, 6], [7, 8, 9]] 1 = [2, 5, 8]
#guard getColumn Nat [[1, 2, 3], [4, 5], [7, 8, 9]] 2 = [3, 9]

def removeIdx (a : Type) (xs : List a) (idx : Nat) : List a :=
  /- Given a list, removes the specified index. If the index is out of range,
    then this function will return the original list.
  -/
  match xs with
    | List.nil => List.nil
    | List.cons y ys =>
      if idx == 0 then
        ys
      else
        List.cons y (removeIdx a ys (idx - 1))

#guard removeIdx Nat [] 0 = []
#guard removeIdx Nat [14] 0 = []
#guard removeIdx Nat [1, 4, 6, 1, 2, 4] 3 = [1, 4, 6, 2, 4]
#guard removeIdx Nat [1, 2, 3, 4] 10 = [1, 2, 3, 4]

/-================================STATISTICS FUNCTIONS================================-/

def stdDev (lst : List Float) : Option Float :=
  /- Given a nonempty list of floats, computes the population standard deviation as an option.
    If the list is empty, returns none -/
  match lst.length with
    | Nat.zero => none
    | Nat.succ _ =>
      let mean := (lst.foldl (fun a b => a + b) 0.0 ) / Float.ofNat lst.length
      let squareDiffs := lst.map (fun x => (x - mean) ^ 2)
      some (Float.sqrt ((squareDiffs.foldl (fun a b => a + b) 0.0) / Float.ofNat lst.length))

#guard stdDev [] == none
#guard stdDev [1.0] == some 0.0
#guard stdDev [1.0, 1.0, 1.0] == some 0.0
#guard stdDev [2, 4, 6, 8] == some (Float.sqrt 5)

def normalizeList (lst : List Float) : List Float :=
  /- Given a list of floats, normalizes and returns the list using z-score normalization.
    If the standard deviation is 0 (every element identical), normalizes everything to 0 -/
  let dev := stdDev lst
  match dev with
    | none => []
    | some v =>
      let mean := (lst.foldl (fun a b => a + b) 0.0 ) / Float.ofNat lst.length
      lst.map (fun x => if v == 0 then 0 else (x - mean) / v)

#guard normalizeList [] == []
#guard normalizeList [1.0] == [0]
#guard normalizeList [1.0, 1.0, 1.0] == [0, 0, 0]
#guard normalizeList [2, 4, 4, 4, 5, 5, 7, 9] == [-1.5, -0.5, -0.5, -0.5, 0, 0, 1, 2]

def meanCols (lst2D : List (List Float)) : List Float :=
  /- Given a 2D list of floats with shape m x n, computes the mean of each column -/
  match lst2D with
    | List.nil => []
    | List.cons y _ =>
      let numCols := y.length
      let colsRange := List.range numCols
      let cols := colsRange.map (fun n => getColumn Float lst2D n)
      cols.map (fun lst => (lst.foldl (fun a b => a + b) 0.0) / Float.ofNat lst.length)

#guard meanCols [] == []
#guard meanCols [[]] == [] --no columns
#guard meanCols [[1]] == [1]
#guard meanCols [[1, 2, 3]] == [1, 2, 3]
#guard meanCols [[1], [2], [3]] == [2]
#guard meanCols [[1, 2, 3], [4, 5, 6], [7, 8, 9]] == [4, 5, 6]

def stdDevCols (lst2D : List (List Float)) : List (Float) :=
  /- Given a 2D list of floats with shape m x n, computes the population standard deviation of each column -/
  match lst2D with
    | List.nil => []
    | List.cons y _ =>
      let numCols := y.length
      let colsRange := List.range numCols
      let cols := colsRange.map (fun n => getColumn Float lst2D n)
      cols.map (fun col =>
        match stdDev col with
          | none => 0 -- the column will never be empty because we only access columns within the range, so stddev will never be none
          | some v => v)

#guard stdDevCols [] == []
#guard stdDevCols [[]] == [] --no columns
#guard stdDevCols [[1, 2, 3]] == [0, 0, 0]
#guard stdDevCols [[0], [10]] == [5]
#guard stdDevCols [[1, 2], [3, 4], [5, 6], [7, 8]] == [(Float.sqrt 5), (Float.sqrt 5)]

def normalizeData (norm2D : List (List Float)) (data2D : List (List Float)): List (List Float) :=
  /- Normalizes each column of a 2D array of floats using z score normalization
    data2D is the data that is being normalized, the norm2D is the data that is being used to compute the mean
    and standard deviation (good for making predictions on new, unseen data)
    if norm2D is empty, resulting data is also empty
  -/
  data2D.map (fun lst => List.map (fun (x, (mu, sig)) =>
    if sig == 0 then 0 else (x - mu) / sig )
  (List.zip lst (List.zip (meanCols norm2D) (stdDevCols norm2D))))

#guard normalizeData [] [] == []
#guard normalizeData [[]] [] == []
#guard normalizeData [] [[1], [1], [1]] == [[], [], []]
#guard normalizeData [[1], [1], [1]] [[1], [1], [1]] == [[0], [0], [0]]
#guard normalizeData [[0], [10]] [[5]] == [[0]]
#guard normalizeData [[1, 2, 3], [-1, -2, -3]] [[1, 2, 3], [-1, -2, -3]] == [[1, 1, 1], [-1, -1, -1]]
#guard normalizeData [[1, 2, 3], [-1, -2, -3]] [[3, 10, -21]] == [[3, 5, -7]]
#guard normalizeData [[2], [4], [4], [4], [5], [5], [7], [9]] [[2], [4], [4], [4], [5], [5], [7], [9]]
  == [[-1.5], [-0.5], [-0.5], [-0.5], [0], [0], [1], [2]]

/-================================GRADIENT DESCENT FUNCTIONS================================-/

def dot (vec1 : List Float) (vec2 : List Float) : Float :=
  /- Computes the doc product between two vectors
    If one list is longer than the others, the excess values are zeroed
  -/
  match vec1 with
    | List.nil => 0
    | List.cons val1 vec1r =>
      match vec2 with
        | List.nil => 0
        | List.cons val2 vec2r =>
          val1 * val2 + (dot vec1r vec2r)

#guard dot [1, 2, 3] [4, 5, 6] == 32
#guard dot [] [] == 0
#guard dot [1, 2] [] == 0
#guard dot [1, 2, 3] [1, 2] == 5
#guard dot [10] [5] == 50
#guard dot [6, 3] [9, 2] == 60

def initWeights (features : Nat) : List Float :=
  /- Given a natural number, returns the 0 vector with that length
  -/
  List.replicate features 0

#guard initWeights 5 == [0, 0, 0, 0, 0]
#guard initWeights 0 == []
#guard initWeights 1 == [0]

def initBias : Float := 0

def MSELoss (X : List (List Float)) (y : List Float) (w : List Float) (b : Float) : Option Float :=
  /- Given input features, weights, biases, and true values, computes the mean squared error as an option
    Returns none if X or y was empty
    X has shape (m, d)
    y has length m
    w has length d
  -/
  let pairs := List.zip X y
  let losses := pairs.map (fun p => (p.snd - ((dot p.fst w) + b)) ^ 2)
  let sumLosses := List.foldl (fun (a: Float) (b: Float) => a + b) 0.0 losses
  let loss := (sumLosses / Float.ofNat losses.length) / 2
  if losses.length == 0 then none else some loss

#guard MSELoss [] [] [0] 0 == none
#guard MSELoss [[1]] [1] [1] 0 == some 0
#guard MSELoss [[1]] [1] [0] 1 == some 0
#guard MSELoss [[1]] [1] [0] 1 == some 0
#guard MSELoss [[5, 0, 0], [2, 3, 2], [4, 1, 1]] [5, 8, 4] [1, 1, 1] 0 == some (5 / 6)
#guard MSELoss [[1, 5, 3, 7], [12, 67, 32, 20]] [20, 200] [2, 1, 3, 1] 10 == some 114.5

def forward (X : List (List Float)) (w : List Float) (b : Float) : List Float :=
  /- Given input features, weights, and biases, computes the forward pass
    X has shape (m, d)
    w has length d
  -/
  X.map (fun x => (dot x w) + b)

#guard forward [[1, 2, 3]] [1, 1, 1] 10 == [16]
#guard forward [] [] 3 == []
#guard forward [[5]] [2] 3 == [13]
#guard forward [[10, 2, 3], [3, 0, -1]] [4, -29, 9] 0 == [9, 3]
#guard forward [[3, 1], [-4, -8], [5, 12], [1, 10]] [2, 1] 5 == [12, -11, 27, 17]

def getDw (pred : List Float) (X : List (List Float)) (y : List Float) : List Float :=
  /- given predictions, features, and true values, computes the gradient for the weights
    X has shape (m, d)
    y, pred have length m
  -/
  let pairs := List.zip pred y
  let diffs := pairs.map (fun p => p.fst - p.snd)
  let n := Float.ofNat diffs.length

  match X.head? with
  | none => []
  | some f =>
    let numFeatures := f.length
    let FeaturesRange := List.range numFeatures
    FeaturesRange.map (fun j =>
      let col := getColumn Float X j
      let sum := (List.range diffs.length).foldl (fun acc i =>
        let featureVal := match List.get? col i with
          | none => 0.0
          | some v => v

        let diffVal := match List.get? diffs i with
          | none => 0.0
          | some v => v

        acc + featureVal * diffVal) 0.0
      sum / n)

#guard getDw [] [] [] == []
#guard getDw [] [[]] [] == []
#guard getDw [0] [[1]] [1] == [-1]
#guard getDw [1, 2, 3, 4] [[1, 1], [2, 2], [3, 3], [4, 4]] [1, 2, 3, 4] == [0, 0]
#guard getDw [1] [[10]] [2] == [-10]
#guard getDw [-5, 10, 13] [[1, 3, -1], [4, 13, 0], [1, 2, 2]] [-3, 7, 16] == [7/3, 9, -4/3]

def getDb (pred : List Float) (y : List Float) : Option Float :=
  /- given predictions and true values, computes the gradient for the bias as an option
    If either list is empty, returns none
    pred and y have length m -/
  let pairs := List.zip pred y
  let diffs := pairs.map (fun p => p.fst - p.snd)
  if diffs.length == 0 then
    none
  else
    some ((diffs.foldl (fun a b => a + b) 0) / Float.ofNat diffs.length)

#guard getDb [] [] == none
#guard getDb [0] [1] == some (-1)
#guard getDb [1, 2, 3, 4] [1, 2, 3, 4] == some 0
#guard getDb [1] [2] == some (-1)
#guard getDb [-5, 10, 13] [-3, 7, 16] == some (-2/3)

def update (w : List Float) (b : Float) (dw : List Float) (db : Float) (lr : Float) : List Float × Float :=
  /- Given weights, biases, their gradients, and the learning rate, returns the updated weights and biases in a tuple -/
  let wAndDw := List.zip w dw
  let updatedW := wAndDw.map (fun p => p.fst - p.snd * lr)
  let updatedB := b - db * lr
  (updatedW, updatedB)

#guard update [] (-1) [] 2 (-1) == ([], 1)
#guard update [10] 1 [5] 2 1 == ([5], -1)
#guard update [1, 2, -1, -4] 10 [1, 2, -1, -4] 10 1 == ([0, 0, 0, 0], 0)
#guard update [0, 0, 0] 0 [-1, -4, 4] 3 (-1) == ([-1, -4, 4], 3)

def trainLoop (X : List (List Float)) (y : List Float) (epochs : Nat) (lr : Float) : Option (List Float × Float) :=
  /- Given training features, true values, number of epochs, and learning rate, runs through the training loop and
    returns the final weights and biases as an option.
    If training data or labels are empty, returns none
    X has shape (m, d)
    y has length m -/
  let rec trainHelp (w : List Float) (b : Float) (epochsLeft : Nat) : Option (List Float × Float) :=
    /- Helper to repeatedly update the weights and biases in the loop -/
    match epochsLeft with
    | Nat.zero => (w, b)
    | Nat.succ n =>
      let pred := forward X w b
      let dw := getDw pred X y
      let db := getDb pred y
      match db with
        | none => none
        | some dbVal =>
          let updatedParams := update w b dw dbVal lr
          trainHelp updatedParams.fst updatedParams.snd n

  match X.head? with
    | none => none
    | some f =>
      trainHelp (initWeights (f.length)) initBias epochs

#guard trainLoop [] [] 1 1 == none
#guard trainLoop [[]] [] 1 1 == none
#guard trainLoop [[1]] [1] 1 1 == some ([1], 1)
#guard trainLoop [[1, 2, 3]] [1] 0 1 == some ([0, 0, 0], 0)
#guard trainLoop [[1, 2, 3], [4, 5, 6]] [2, 5] 1 1 == some ([11, 14.5, 18], 3.5)
#guard trainLoop [[1, 2, 3], [4, 5, 6]] [1, 1] 2 1 == some ([-118, -155.75, -193.5], -37.75)

def predictor (w : List Float) (b : Float) (X : List (List Float)) (y : List Float) : Option (List (List Float) -> (List Float)) :=
  /- Given normalized weights, biases, and the features and labels that were used for normalization, returns a predictor function
    that can take in a list of features and return a list of predictions.
    If list of labels is empty, returns none
    X has shape (m, d)
    y has length m
    w has length d
  -/
  let yMean := (y.foldl (fun a b => a + b) 0.0) / Float.ofNat y.length
  let yStd := stdDev y
  match yStd with
    | none => none
    | some yStdVal =>
    let predict (x : List (List Float)) : List Float :=
      let xNorm := normalizeData X x
      let predNorm := forward xNorm w b
      predNorm.map (fun x => x * yStdVal + yMean)
    predict

#guard (predictor [0] 0 [] []).isNone
#guard (predictor [1] 0 [[1]] [1]).get! [[1]] == [1]
#guard (predictor [-5, 3, 0] 10 [[1, 2, 3], [-1, -2, -3]] [13, 7]).get! [[12, 6, 3], [1, 2, 3], [0, 0, 0]] == [-113, 34, 40]
#guard (predictor [2] (0) [[2], [4], [4], [4], [5], [5], [7], [9]] [4, 8, 8, 8, 10, 10, 14, 18]).get! [[20], [40], [10]] == [70, 150, 30]
