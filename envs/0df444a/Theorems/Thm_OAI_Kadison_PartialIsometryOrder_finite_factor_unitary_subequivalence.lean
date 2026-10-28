-- Prove2me | Theorems.Thm_OAI_Kadison_PartialIsometryOrder_finite_factor_unitary_subequivalence
-- name    : OAI.Kadison.PartialIsometryOrder.finite_factor_unitary_subequivalence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:47:46.571297+00:00
-- url     : https://prove2.me/theorems/88aa7fd1-080d-4e6f-bcd3-209bfc2717bb
-- title:
--   OAI.Kadison.PartialIsometryOrder.finite_factor_unitary_subequivalence: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PartialIsometryOrder`, with `open scoped ComplexOrder`):
--
--   ```lean
--   theorem finite_factor_unitary_subequivalence (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
--       (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
--       (e f : M) (he : IsStarProjection e) (hf : IsStarProjection f)
--       (hle : τ e≤τ f) : ∃ u : unitary M,(u:M)*e*star (u:M)≤f
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CornerTransport.finite_small_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_factor_unitary_subequivalence (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (e f : M) (he : IsStarProjection e) (hf : IsStarProjection f)
    (hle : τ e≤τ f) : ∃ u : unitary M,(u:M)*e*star (u:M)≤f := by
  sorry

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end
