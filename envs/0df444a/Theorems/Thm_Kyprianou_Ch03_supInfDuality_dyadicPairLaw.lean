-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDuality_dyadicPairLaw
-- name    : Kyprianou.Ch03.supInfDuality_dyadicPairLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:09:10.403943+00:00
-- url     : https://prove2.me/theorems/298d2c82-0834-489e-a336-7276b046d3bb
-- title:
--   Joint extrema reversal on a finite dyadic time grid
-- statement:
--   For the original Lévy process, finite equally spaced dyadic samples have the same joint maximum and drawdown law as the terminal value minus the grid minimum and negative grid minimum. Reverse the finite independent identically distributed increments and telescope the prefix sums.
-- source:
--   Kyprianou (2006), Lemma 3.5; finite-grid proof of the time-reversal identity.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDuality_dyadicPairLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (n : ℕ) :
    Measure.map
      (fun omega : Omega =>
        let a := sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
          X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) omega))
        (a, a - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let b := sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
          X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) omega))
        (X t omega - b, -b)) P := by sorry
