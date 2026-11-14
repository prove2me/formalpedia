-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_exists_core_perturbationData
-- name    : OAI.WeakPureInfiniteness.exists_core_perturbationData
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:14:29.574161+00:00
-- url     : https://prove2.me/theorems/0d172211-5e48-4607-b81a-7f6008ab4c8d
-- title:
--   OAI.WeakPureInfiniteness.exists_core_perturbationData: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.exists_core_perturbationData` of [lean/OAI/Analysis/WeakInfiniteness/SquareZero.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/SquareZero.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open scoped CStarAlgebra Topology`):
--
--   ```lean
--   lemma exists_core_perturbationData {n : ℕ} (hn : 1 ≤ n)
--       (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
--       {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : NonUnitalRepresentationIrreducible π)
--       {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u*v=0) (hun : π u ≠ 0) (hvn : π v ≠ 0) :
--       ∃ F : OrthogonalPerturbationData A n,
--         F.p ∈ hereditarySubalgebra u hu.isSelfAdjoint ∧
--         F.q ∈ hereditarySubalgebra v hv.isSelfAdjoint ∧ π (positiveCut F.α F.c) ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.NonUnitalRepresentationIrreducible`, `OAI.WeakPureInfiniteness.OrthogonalPerturbationData`, `OAI.WeakPureInfiniteness.hereditarySubalgebra` and `OAI.WeakPureInfiniteness.positiveCut` (definitions bundle `OAIQ246W001` of this split); `OAI.WeakPureInfiniteness.ProperlyInfinite` and `OAI.WeakPureInfiniteness.diagonalCopies` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.exists_square_zero_on_norm_slice_of_gap_any` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/SquareZero.lean (declaration OAI.WeakPureInfiniteness.exists_core_perturbationData)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W001

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

open scoped CStarAlgebra Topology

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma exists_core_perturbationData {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : NonUnitalRepresentationIrreducible π)
    {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u*v=0) (hun : π u ≠ 0) (hvn : π v ≠ 0) :
    ∃ F : OrthogonalPerturbationData A n,
      F.p ∈ hereditarySubalgebra u hu.isSelfAdjoint ∧
      F.q ∈ hereditarySubalgebra v hv.isSelfAdjoint ∧ π (positiveCut F.α F.c) ≠ 0 := by
  sorry

end

end WeakPureInfiniteness
end

end OAI
end
