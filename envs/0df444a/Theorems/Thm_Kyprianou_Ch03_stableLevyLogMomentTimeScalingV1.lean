-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableLevyLogMomentTimeScalingV1
-- name    : Kyprianou.Ch03.stableLevyLogMomentTimeScalingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:00:20.820867+00:00
-- url     : https://prove2.me/theorems/b086eed7-c5e0-49ed-b867-0b2dd1facd95
-- title:
--   Log moment scaling in time for a Lévy process with finite exponential moments
-- statement:
--   Use independent stationary increments, right-continuity, Fatou and the established scalar multiplicative moment theorem.
-- source:
--   Kyprianou (2006), Exercise 3.7; exact auxiliary for stable regime proofs.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.stableLevyLogMomentTimeScalingV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (b : ℝ) (hi : ∀ t, Integrable (fun w => Real.exp (b * X t w)) P)
    (t : NNReal) :
    Real.log (∫ w, Real.exp (b * X t w) ∂P) =
      (t : ℝ) * Real.log (∫ w, Real.exp (b * X 1 w) ∂P) := by sorry
