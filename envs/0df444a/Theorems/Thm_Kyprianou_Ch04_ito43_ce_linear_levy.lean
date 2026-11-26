-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ce_linear_levy
-- name    : Kyprianou.Ch04.ito43_ce_linear_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:09:43.698822+00:00
-- url     : https://prove2.me/theorems/f29afa9b-b386-5710-9be8-e55eabe866c9
-- title:
--   Deterministic unit drift has zero Gaussian variance and the drift Levy triplet
-- statement:
--   Deterministic unit drift has zero Gaussian variance and the drift Levy triplet.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3 formalisation boundary audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Deterministic unit drift has the unit-drift, zero-variance, zero-jump triplet. -/

theorem Kyprianou.Ch04.ito43_ce_linear_levy {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    let X : NNReal → Ω → ℝ := fun t _ => (t : ℝ)
    ∃ tr : LevyKhintchineTriple, IsLevyProcess X P ∧ tr.gaussianVariance = 0 ∧
      ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ) := by sorry
