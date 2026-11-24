-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDuality_of_dyadicPairLaws
-- name    : Kyprianou.Ch03.supInfDuality_of_dyadicPairLaws
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:09:11.366564+00:00
-- url     : https://prove2.me/theorems/bf2d9bef-0c14-4af5-a55a-1c004b63cba5
-- title:
--   Passage from dyadic joint extrema laws to continuous-time extrema
-- statement:
--   If the joint reversal identity holds on every finite dyadic grid of the original Lévy process, it holds for the continuous-time extrema. On almost every càdlàg path, the grids include both endpoints, their extrema converge to the actual extrema by right continuity, and the pushforward identities pass to the limit by bounded continuous tests.
-- source:
--   Kyprianou (2006), Lemma 3.5; dyadic approximation and uniqueness of probability laws.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDuality_of_dyadicPairLaws
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (hGrid : ∀ n : ℕ,
      Measure.map
      (fun omega : Omega =>
        let a := sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
          X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) omega))
        (a, a - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let b := sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
          X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) omega))
        (X t omega - b, -b)) P) :
    Measure.map
      (fun omega : Omega =>
        let a := LevyExtrema.SBA.runSup (fun s => X s omega) t
        (a, a - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let b := sInf ((fun s : NNReal => X s omega) '' Set.Icc 0 t)
        (X t omega - b, -b)) P := by sorry
