-- Prove2me | Theorems.Thm_OAI_QuarticPowerFree_quartic_generic_threshold_uniform
-- name    : OAI.QuarticPowerFree.quartic_generic_threshold_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T15:07:16.341258+00:00
-- url     : https://prove2.me/theorems/85f08670-b12c-4a5d-a98b-ce26224690c9
-- title:
--   OAI.QuarticPowerFree.quartic_generic_threshold_uniform: intermediate lemma from OpenAI, Squarefree values of quartics and power-free values of polynomials
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.QuarticPowerFree.allDegrees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Squarefree values of quartics and power-free values of polynomials*, OpenAI Math Release, September 24, 2026, result family 20, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.QuarticPowerFree.quartic_generic_threshold_uniform` of [lean/OAI/NumberTheory/PowerFree/QuarticComponents.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/QuarticComponents.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.QuarticPowerFree`, with `open MvPolynomial`):
--
--   ```lean
--   theorem quartic_generic_threshold_uniform {n h : ℕ} (j : Fin 100)
--       (hh : 3 ≤ h) (hh' : h ≤ 4) (E D : ℕ) (hD : 0 < D) :
--       ∃ C : ℝ, 0 ≤ C ∧
--         ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
--           (a b : Fin 4 → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
--           (θ : Fin 4 → ℂ), Function.Injective θ →
--         (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
--         (∀ i, Ideal.Quotient.mk I (a i)^2*Ideal.Quotient.mk I (b i) =
--           Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
--         Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤ →
--         Transcendental ℂ (Ideal.Quotient.mk I q) → affineDimension I = h → affineDegree I ≤ E →
--         (∀ i, (a i).totalDegree ≤ D) → q.totalDegree ≤ D →
--         ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
--           (∀ i, a i ∈ weightedSpace w (quarticA j)) → (∀ i, b i ∈ weightedSpace w (quarticB j)) →
--         ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = 400*ω i) →
--         ∀ T : ℝ, 1 ≤ T →
--           T^h/((h.factorial:ℝ)*(quarticEnvelope j h)^h)-C*T^(h-1) ≤ weightedHilbert I ω T
--   ```
--
--   **Definitions.** The statement is written with `OAI.QuarticPowerFree.affineDegree`, `OAI.QuarticPowerFree.affineDimension`, `OAI.QuarticPowerFree.quarticA`, `OAI.QuarticPowerFree.quarticB`, `OAI.QuarticPowerFree.quarticEnvelope`, `OAI.QuarticPowerFree.weightedHilbert` and `OAI.QuarticPowerFree.weightedSpace` (definitions bundle `OAIB3Qp000` of this split).
--
--   **Used by.** The proof of `OAI.QuarticPowerFree.quartic_dyadic_tail` of this split imports it.
-- source:
--   OpenAI, Squarefree values of quartics and power-free values of polynomials, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 20; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/QuarticComponents.lean (declaration OAI.QuarticPowerFree.quartic_generic_threshold_uniform)

import Mathlib
import Definitions.Def_OAIB3Qp000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open MvPolynomial

theorem quartic_generic_threshold_uniform {n h : ℕ} (j : Fin 100)
    (hh : 3 ≤ h) (hh' : h ≤ 4) (E D : ℕ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
        (a b : Fin 4 → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
        (θ : Fin 4 → ℂ), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^2*Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤ →
      Transcendental ℂ (Ideal.Quotient.mk I q) → affineDimension I = h → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → q.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w (quarticA j)) → (∀ i, b i ∈ weightedSpace w (quarticB j)) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = 400*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        T^h/((h.factorial:ℝ)*(quarticEnvelope j h)^h)-C*T^(h-1) ≤ weightedHilbert I ω T := by
  sorry

open MvPolynomial
open scoped Classical BigOperators

end QuarticPowerFree

end OAI
end
