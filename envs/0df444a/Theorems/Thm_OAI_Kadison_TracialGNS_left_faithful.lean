-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_left_faithful
-- name    : OAI.Kadison.TracialGNS.left_faithful
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:37.592725+00:00
-- url     : https://prove2.me/theorems/6dcc9e04-8fa1-4033-a229-f66b41890cbd
-- title:
--   OAI.Kadison.TracialGNS.left_faithful: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`):
--
--   ```lean
--   lemma left_faithful (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) :
--       Function.Injective τ.gnsStarAlgHom
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.finite_standard_gauge_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

lemma left_faithful (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) :
    Function.Injective τ.gnsStarAlgHom := by
  sorry

end TracialGNS

end Kadison
end

end OAI
end
