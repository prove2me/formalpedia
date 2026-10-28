-- Prove2me | Theorems.Thm_OAI_Kadison_PreHilbert_operator_ext_dense_stages
-- name    : OAI.Kadison.PreHilbert.operator_ext_dense_stages
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:37:30.202556+00:00
-- url     : https://prove2.me/theorems/44ee1502-7001-4715-8576-f492e6c1348b
-- title:
--   OAI.Kadison.PreHilbert.operator_ext_dense_stages: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PreHilbert`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`):
--
--   ```lean
--   theorem operator_ext_dense_stages (E F : PreHilbert) (k l : ℕ)
--       (S : ℕ → Set E) (R : ℕ → Set F) (hS : Monotone S) (hR : Monotone R)
--       (hSd : Dense (⋃ n, S n)) (hRd : Dense (⋃ n, R n))
--       (T U : wordSpace E F k →L[ℂ] wordSpace E F l)
--       (h : ∀ n d, d ∈ S n → ∀ x, (∀ i, x i ∈ R n) → ∀ c, c ∈ S n →
--         ∀ y, (∀ j, y j ∈ R n) →
--         inner ℂ (word E F l c y) (T (word E F k d x)) =
--           inner ℂ (word E F l c y) (U (word E F k d x))) : T = U
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power`, `OAI.Kadison.PreHilbert.word` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.word_multiplicity_slices` of this split imports it.
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
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.PreHilbert

theorem operator_ext_dense_stages (E F : PreHilbert) (k l : ℕ)
    (S : ℕ → Set E) (R : ℕ → Set F) (hS : Monotone S) (hR : Monotone R)
    (hSd : Dense (⋃ n, S n)) (hRd : Dense (⋃ n, R n))
    (T U : wordSpace E F k →L[ℂ] wordSpace E F l)
    (h : ∀ n d, d ∈ S n → ∀ x, (∀ i, x i ∈ R n) → ∀ c, c ∈ S n →
      ∀ y, (∀ j, y j ∈ R n) →
      inner ℂ (word E F l c y) (T (word E F k d x)) =
        inner ℂ (word E F l c y) (U (word E F k d x))) : T = U := by
  sorry

end Kadison.PreHilbert
end

end OAI
end
