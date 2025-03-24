import LinearRegression
import LinearRegression.HousingData

def dataSize := data.length
def splitAt := dataSize * 4 / 5

def X := data.map (fun x => removeIdx Float x (headers.idxOf "Price"))
def y := getColumn Float data (headers.idxOf "Price")

def XNorm := normalizeData X X
def yMean := (y.foldl (fun a b => a + b) 0.0) / Float.ofNat y.length
def yNorm := normalizeList y

def XTrainNorm := (List.splitAt splitAt XNorm).fst
def XTestNorm := (List.splitAt splitAt XNorm).snd
def yTrainNorm := (List.splitAt splitAt yNorm).fst
def yTestNorm := (List.splitAt splitAt yNorm).snd

def main : IO Unit := do
  -- Training
  let params := trainLoop XTrainNorm yTrainNorm 10000 0.001
  let finalW := params.get!.fst
  let finalB := params.get!.snd
  let trainLoss := MSELoss XTrainNorm yTrainNorm finalW finalB
  let testLoss := MSELoss XTestNorm yTestNorm finalW finalB

  IO.println s!"Normalized weights (income, age, rooms, bedrooms, population): {finalW}"
  IO.println s!"Normalized bias: {finalB}"
  IO.println s!"Training Loss: {trainLoss.get!}"
  IO.println s!"Testing Loss: {testLoss.get!}"

  let testIncome := 150000
  let testAge := 10
  let testRooms := 7
  let testBedrooms := 3
  let testPopulation := 50000
  let testFeatures := [testIncome, testAge, testRooms, testBedrooms, testPopulation]
  let predictFun := (predictor finalW finalB X y).get!
  let testPrediction := predictFun [testFeatures]
  IO.println "Example prediction: "
  IO.println s!"Income: {testIncome}"
  IO.println s!"Age: {testAge}"
  IO.println s!"Number of rooms: {testRooms}"
  IO.println s!"Number of bedrooms: {testBedrooms}"
  IO.println s!"Population: {testPopulation}"
  IO.println s!"Prediction: {testPrediction}"
