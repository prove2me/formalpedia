-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_levy_cosine_increment_bound
-- name    : Kyprianou.Ch04.ito43_levy_cosine_increment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:09:08.844957+00:00
-- url     : https://prove2.me/theorems/4fb010f5-564e-4403-b989-0b36c31654db
-- title:
--   Cosine deficit of a small Levy increment is linear in duration
-- statement:
--   The expected nonnegative cosine deficit of a deterministic Levy increment is at most twice its duration times the norm of the characteristic exponent when this product is at most one.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A small deterministic Levy increment has a cosine deficit of order its duration.
No second-moment hypothesis on the Levy process is required. -/

theorem Kyprianou.Ch04.ito43_levy_cosine_increment_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (s h : NNReal) (ξ : ℝ)
    (hh : (h : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ ≤ 1) :
    let F : Ω → ℝ := fun w => 1 - Real.cos (ξ * (X (s+h) w - X s w))
    Integrable F P ∧
      (∀ w, 0 ≤ F w) ∧
      (∫ w, F w ∂P) ≤ 2 * (h : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ := by sorry
