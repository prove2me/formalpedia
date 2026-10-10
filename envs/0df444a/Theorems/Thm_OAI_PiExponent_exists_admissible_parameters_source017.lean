-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_admissible_parameters_source017
-- name    : OAI.PiExponent.exists_admissible_parameters_source017
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:44:44.767577+00:00
-- url     : https://prove2.me/theorems/fdcbce8c-d9e6-43dd-8587-cfe865e6e78a
-- title:
--   Existence of admissible approximation parameters for pi
-- statement:
--   Given ν ∈ ℝ with ν > 2 and Λ,c ∈ ℝ with Λ > 0 and c > 0, suppose hbad: ∀ Q ∈ ℕ, ∃ p ∈ ℤ, ∃ q ∈ ℕ, Q ≤ q ∧ |π - p/q| ≤ q^(−ν). Then there exists a tuple in the published AdmissibleParameters structure, with ε > 0, m ≥ 1, normalized rational approximations, and the stated approximation, dimension, collision, and weight-error margins, including a positive minimum weight.
--
--   Display formula: $$h_{\mathrm{bad}} : \forall Q \in \mathbb{N},\; \exists p \in \mathbb{Z}, q \in \mathbb{N},\; Q \le q \land \left|\pi-\frac{p}{q}\right| \le q^{-\nu}.$$
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean#L105-L220

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters
import Mathlib

theorem OAI.PiExponent.exists_admissible_parameters_source017
    (nu Lambda c : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (AdmissibleParameters nu Lambda c) := by
  sorry
