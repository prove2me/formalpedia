-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableHighIndexNoIntegerMomentsV1
-- name    : Kyprianou.Ch03.stableHighIndexNoIntegerMomentsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T17:59:54.62021+00:00
-- url     : https://prove2.me/theorems/d74de679-dad0-42b5-adb6-e419984edd82
-- title:
--   Nonintegrability of integer moments for a stable process of index below two
-- statement:
--   Transfer a hypothetical unit-time moment to all times via the supplied strict scaling law, then contradict the fractional-moment criterion since n≥2>alpha.
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

theorem Kyprianou.Ch03.stableHighIndexNoIntegerMomentsV1
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
      ∀ n : ℕ, 2 ≤ n →
        ¬ Integrable (fun omega => |X 1 omega| ^ n) P := by sorry
