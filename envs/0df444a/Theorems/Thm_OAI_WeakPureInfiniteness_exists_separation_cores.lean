-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_exists_separation_cores
-- name    : OAI.WeakPureInfiniteness.exists_separation_cores
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:14:39.918671+00:00
-- url     : https://prove2.me/theorems/5a257de7-7f5d-42e0-84d8-2d43b2507b0e
-- title:
--   OAI.WeakPureInfiniteness.exists_separation_cores: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.exists_separation_cores` of [lean/OAI/Analysis/WeakInfiniteness/SeparationCoreSelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/SeparationCoreSelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open scoped CStarAlgebra`):
--
--   ```lean
--   lemma exists_separation_cores
--       (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
--       (X : A) {l : ℝ} (hl : 0 < l) :
--       let g := cfcₙ (separationG l) (star X*X)
--       ∃ e f k₁ k₂ : A,0 ≤ e ∧ 0 ≤ f ∧ 0 ≤ k₁ ∧ 0 ≤ k₂ ∧
--         ‖e‖ ≤ 1 ∧ ‖f‖ ≤ 1 ∧ e*f=0 ∧ e*star e*k₁=k₁ ∧ f*star f*k₂=k₂ ∧
--         g*e=e ∧ g*f=f ∧
--         ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
--           4*l ≤ ‖π X‖ → π k₁ ≠ 0 ∧ π k₂ ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.separationG` (definitions bundle `OAIQ246W001` of this split); `OAI.WeakPureInfiniteness.ComplexHilbert`, `OAI.WeakPureInfiniteness.ProperlyInfinite` and `OAI.WeakPureInfiniteness.diagonalCopies` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.quantitative_separatingPositives_any` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/SeparationCoreSelection.lean (declaration OAI.WeakPureInfiniteness.exists_separation_cores)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W001

section

attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal _root_.OAI.WeakPureInfiniteness.supportedAlgebra_isClosed _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

open scoped CStarAlgebra

universe u v

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma exists_separation_cores
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    (X : A) {l : ℝ} (hl : 0 < l) :
    let g := cfcₙ (separationG l) (star X*X)
    ∃ e f k₁ k₂ : A,0 ≤ e ∧ 0 ≤ f ∧ 0 ≤ k₁ ∧ 0 ≤ k₂ ∧
      ‖e‖ ≤ 1 ∧ ‖f‖ ≤ 1 ∧ e*f=0 ∧ e*star e*k₁=k₁ ∧ f*star f*k₂=k₂ ∧
      g*e=e ∧ g*f=f ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        4*l ≤ ‖π X‖ → π k₁ ≠ 0 ∧ π k₂ ≠ 0 := by
  sorry

end

end

end WeakPureInfiniteness
end

end OAI
end
