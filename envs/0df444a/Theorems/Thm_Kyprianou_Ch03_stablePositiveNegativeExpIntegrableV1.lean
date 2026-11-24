-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stablePositiveNegativeExpIntegrableV1
-- name    : Kyprianou.Ch03.stablePositiveNegativeExpIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:00:45.965831+00:00
-- url     : https://prove2.me/theorems/3ce0d2e3-eed7-4590-930b-ea93291cb073
-- title:
--   Negative exponential moments for positive stable Lévy measures
-- statement:
--   Use the exponential moment criterion and the bounded negative exponential on the positive large-jump support.
-- source:
--   Kyprianou (2006), Exercise 3.7; exact auxiliary for stable regime proofs.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.stablePositiveNegativeExpIntegrableV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (T : LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure = temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega))
    (theta : ℝ) (htheta : 0 ≤ theta) :
    ∀ t : NNReal, Integrable (fun w => Real.exp (-theta * X t w)) P := by sorry
