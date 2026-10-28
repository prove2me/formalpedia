-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_trace_word_second_order_bound
-- name    : OAI.Kadison.FinitePatching.trace_word_second_order_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:34:11.810556+00:00
-- url     : https://prove2.me/theorems/7aece383-93e2-442a-af36-54c4a75ab5ba
-- title:
--   OAI.Kadison.FinitePatching.trace_word_second_order_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma trace_word_second_order_bound (τ : A →ₗ[ℂ] ℂ) (old new : I → A)
--       (l : List I) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D)
--       (hsingle : ∀ s i t, l=s++i::t →
--         ‖τ (wordProduct old s*new i*wordProduct old t)‖ ≤ S)
--       (hdouble : ∀ s i t j r, l=s++i::(t++j::r) →
--         ‖τ (wordProduct old s*new i*wordProduct old t*new j*
--           wordProduct (fun k => old k+new k) r)‖ ≤ D) :
--       ‖τ (wordProduct (fun i => old i+new i) l)-τ (wordProduct old l)‖ ≤
--         (l.length:ℝ)*S+(l.length:ℝ)^2*D
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FinitePatching.wordProduct` (definitions bundle `OAIQ039C010` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.Words.word_perturbation_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.FinitePatching

variable {A I : Type*} [NormedRing A]

variable [NormedAlgebra ℂ A]

lemma trace_word_second_order_bound (τ : A →ₗ[ℂ] ℂ) (old new : I → A)
    (l : List I) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hsingle : ∀ s i t, l=s++i::t →
      ‖τ (wordProduct old s*new i*wordProduct old t)‖ ≤ S)
    (hdouble : ∀ s i t j r, l=s++i::(t++j::r) →
      ‖τ (wordProduct old s*new i*wordProduct old t*new j*
        wordProduct (fun k => old k+new k) r)‖ ≤ D) :
    ‖τ (wordProduct (fun i => old i+new i) l)-τ (wordProduct old l)‖ ≤
      (l.length:ℝ)*S+(l.length:ℝ)^2*D := by
  sorry

end Kadison.FinitePatching

end

end
end

end OAI
end
