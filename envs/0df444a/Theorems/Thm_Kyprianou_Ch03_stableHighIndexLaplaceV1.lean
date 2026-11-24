-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableHighIndexLaplaceV1
-- name    : Kyprianou.Ch03.stableHighIndexLaplaceV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T17:59:55.32239+00:00
-- url     : https://prove2.me/theorems/8d8d637d-5e55-437e-a81a-2f3fbca4cf25
-- title:
--   Positive log-Laplace coefficient for a spectrally positive stable process of index above one
-- statement:
--   Use integrability of negative exponential moments, stable scaling and the multiplicative moment identity, then strict Jensen with zero first moment.
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

theorem Kyprianou.Ch03.stableHighIndexLaplaceV1
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
      ∃ C : ℝ, 0 < C ∧
        ∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega, Real.exp (-theta * X 1 omega) ∂P) =
            C * theta ^ alpha := by sorry
