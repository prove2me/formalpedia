-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_separation_core_comparisons
-- name    : OAI.WeakPureInfiniteness.separation_core_comparisons
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:27.262201+00:00
-- url     : https://prove2.me/theorems/11f85ae6-e0cd-482d-9a02-4ae640eb2028
-- title:
--   OAI.WeakPureInfiniteness.separation_core_comparisons: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.separation_core_comparisons` of [lean/OAI/Analysis/WeakInfiniteness/SeparationSupport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/SeparationSupport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open scoped CStarAlgebra`):
--
--   ```lean
--   lemma separation_core_comparisons
--       (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
--       (X C k : A) (hk : 0 ≤ k) {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ)
--       (hkdet : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),4*l ≤ ‖π X‖ → π k ≠ 0) :
--       let g := cfcₙ (separationG l) (star X*X)
--       let N := cfcₙ (separationN l) (star X*X)
--       let h := cfcₙ (columnCoreFunction τ) (star (C*g)*(C*g))
--       let d := cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N))
--       ElementCuntzSubequiv d h ∧ ElementCuntzSubequiv d k
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.ElementCuntzSubequiv` (definitions bundle `OAIQ246W000` of this split); `OAI.WeakPureInfiniteness.columnCoreFunction`, `OAI.WeakPureInfiniteness.separationG` and `OAI.WeakPureInfiniteness.separationN` (definitions bundle `OAIQ246W001` of this split); `OAI.WeakPureInfiniteness.ComplexHilbert`, `OAI.WeakPureInfiniteness.ProperlyInfinite` and `OAI.WeakPureInfiniteness.diagonalCopies` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.quantitative_separatingPositives_any` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/SeparationSupport.lean (declaration OAI.WeakPureInfiniteness.separation_core_comparisons)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W000
import Definitions.Def_OAIQ246W001

section

attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

lemma separation_core_comparisons
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    (X C k : A) (hk : 0 ≤ k) {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ)
    (hkdet : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),4*l ≤ ‖π X‖ → π k ≠ 0) :
    let g := cfcₙ (separationG l) (star X*X)
    let N := cfcₙ (separationN l) (star X*X)
    let h := cfcₙ (columnCoreFunction τ) (star (C*g)*(C*g))
    let d := cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N))
    ElementCuntzSubequiv d h ∧ ElementCuntzSubequiv d k := by
  sorry

end

end

end WeakPureInfiniteness
end

end OAI
end
