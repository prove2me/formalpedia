-- Prove2me | Theorems.Thm_OAI_Lech_finite_module_tensor_asymptoticENN
-- name    : OAI.Lech.finite_module_tensor_asymptoticENN
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:06:06.778847+00:00
-- url     : https://prove2.me/theorems/a776caea-fb98-46b6-bd42-2fb121d57913
-- title:
--   OAI.Lech.finite_module_tensor_asymptoticENN: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open scoped TensorProduct ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem finite_module_tensor_asymptoticENN (A E : Type*) [CommRing A] [IsDomain A]
--       [IsNoetherianRing A] [AddCommGroup E] [Module A E] [Module.Finite A E]
--       (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : E →ₗ[A] E) ≠ 0) :
--       ∃ r : ℕ, 0 < r ∧ ∀ (N : ℕ → Type*) [∀ q, AddCommGroup (N q)] [∀ q, Module A (N q)]
--         (I : ℕ → Ideal A) (w : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (b : ℕ),
--         (∀ q, Module.length A (N q) ≠ ⊤) →
--         (∀ q, I q ≤ Module.annihilator A (N q)) →
--         (∀ q, ∃ f : (Fin b → A) →ₗ[A] N q, Function.Surjective f) →
--         Tendsto (fun q => w q * (Module.length A (N q)).toENNReal) atTop (𝓝 a) →
--         (∀ g : A, g ≠ 0 → Tendsto (fun q =>
--           w q * (Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toENNReal) atTop (𝓝 0)) →
--         Tendsto (fun q => w q * (Module.length A ((N q) ⊗[A] E)).toENNReal)
--           atTop (𝓝 ((r : ℝ≥0∞) * a))
--   ```
--
--   **Used by.** The proof of `OAI.Lech.exists_frobenius_tensor_transfer` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech
variable {A : Type*} [CommRing A]

open Filter
open scoped Topology

theorem finite_module_tensor_asymptoticENN (A E : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : E →ₗ[A] E) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ (N : ℕ → Type*) [∀ q, AddCommGroup (N q)] [∀ q, Module A (N q)]
      (I : ℕ → Ideal A) (w : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (b : ℕ),
      (∀ q, Module.length A (N q) ≠ ⊤) →
      (∀ q, I q ≤ Module.annihilator A (N q)) →
      (∀ q, ∃ f : (Fin b → A) →ₗ[A] N q, Function.Surjective f) →
      Tendsto (fun q => w q * (Module.length A (N q)).toENNReal) atTop (𝓝 a) →
      (∀ g : A, g ≠ 0 → Tendsto (fun q =>
        w q * (Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toENNReal) atTop (𝓝 0)) →
      Tendsto (fun q => w q * (Module.length A ((N q) ⊗[A] E)).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞) * a)) := by
  sorry

end Lech

end

end OAI
end
