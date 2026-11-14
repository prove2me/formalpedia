-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_exists_binary_splitting_over_norm_slice_any
-- name    : OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:14:17.244893+00:00
-- url     : https://prove2.me/theorems/96ef4da3-5eaa-4451-a779-a5869c97860d
-- title:
--   OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any` of [lean/OAI/Analysis/WeakInfiniteness/UniverseIndividualInfiniteness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/UniverseIndividualInfiniteness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder`):
--
--   ```lean
--   lemma exists_binary_splitting_over_norm_slice_any
--       (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
--       (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
--       {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (j : ℕ) :
--       ∃ z : A,0 ≤ z ∧ CuntzSubequiv (diagonalCopies (2^j) z) (diagonalCopies 1 a) ∧
--         ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),r ≤ ‖π a‖ → π z ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.ComplexHilbert`, `OAI.WeakPureInfiniteness.CuntzSubequiv`, `OAI.WeakPureInfiniteness.Exact`, `OAI.WeakPureInfiniteness.ProperlyInfinite` and `OAI.WeakPureInfiniteness.diagonalCopies` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/UniverseIndividualInfiniteness.lean (declaration OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder

universe u

section UniverseOne

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_binary_splitting_over_norm_slice_any
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ∃ z : A,0 ≤ z ∧ CuntzSubequiv (diagonalCopies (2^j) z) (diagonalCopies 1 a) ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),r ≤ ‖π a‖ → π z ≠ 0 := by
  sorry

end UniverseOne

end

end WeakPureInfiniteness
end

end OAI
end
