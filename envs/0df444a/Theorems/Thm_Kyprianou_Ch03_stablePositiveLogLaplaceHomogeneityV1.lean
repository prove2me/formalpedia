-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stablePositiveLogLaplaceHomogeneityV1
-- name    : Kyprianou.Ch03.stablePositiveLogLaplaceHomogeneityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:00:54.256586+00:00
-- url     : https://prove2.me/theorems/014b1524-ff89-4f39-9d55-e2c759124489
-- title:
--   Homogeneous log Laplace transform of a strictly stable process
-- statement:
--   Combine strict scaling with log moment scaling in time at time theta^alpha, separately treating theta=0.
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

theorem Kyprianou.Ch03.stablePositiveLogLaplaceHomogeneityV1
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
    Real.log (∫ w, Real.exp (-theta * X 1 w) ∂P) =
      Real.log (∫ w, Real.exp (-X 1 w) ∂P) * theta ^ alpha := by sorry
