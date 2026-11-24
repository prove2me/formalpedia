-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableHighIndexUnitIntervalVariationV1
-- name    : Kyprianou.Ch03.stableHighIndexUnitIntervalVariationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T18:00:10.993922+00:00
-- url     : https://prove2.me/theorems/c247904c-78ae-4a4a-bb17-dd1f46e7ee68
-- title:
--   Unbounded variation on the unit interval for a stable process of index above one
-- statement:
--   The first jump moment diverges at zero. Use independent increments, scaling and the bounded-variation criterion to obtain almost sure infinite variation on the unit interval.
-- source:
--   Kyprianou (2006), Exercise 3.7; exact conjunct of stableVariation_highIndexLaplaceAndUnboundedVariation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem Kyprianou.Ch03.stableHighIndexUnitIntervalVariationV1
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega)) :
    1 < alpha →
      ∀ᵐ omega ∂P, ∀ M : ℝ,
        ∃ n : ℕ, ∃ times : Fin (n + 1) → NNReal,
          times 0 = 0 ∧ times (Fin.last n) ≤ 1 ∧
          (∀ i : Fin n, times i.castSucc < times i.succ) ∧
          M < ∑ i : Fin n,
            |X (times i.succ) omega - X (times i.castSucc) omega| := by sorry
