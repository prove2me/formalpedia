-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_quantitative_separatingPositives_any
-- name    : OAI.WeakPureInfiniteness.quantitative_separatingPositives_any
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:22:02.346313+00:00
-- url     : https://prove2.me/theorems/3d0bd3b4-2f97-4419-9e27-bf2755572805
-- title:
--   OAI.WeakPureInfiniteness.quantitative_separatingPositives_any: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.quantitative_separatingPositives_any` of [lean/OAI/Analysis/WeakInfiniteness/QuantitativeSeparation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/QuantitativeSeparation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open scoped CStarAlgebra`):
--
--   ```lean
--   theorem quantitative_separatingPositives_any
--       (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
--       {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hpert : UniformPerturbationOne_any A σ) :
--       QuantitativeSeparatingPositives A σ
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.QuantitativeSeparatingPositives` and `OAI.WeakPureInfiniteness.UniformPerturbationOne_any` (definitions bundle `OAIQ246W003` of this split); `OAI.WeakPureInfiniteness.ProperlyInfinite` and `OAI.WeakPureInfiniteness.diagonalCopies` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/QuantitativeSeparation.lean (declaration OAI.WeakPureInfiniteness.quantitative_separatingPositives_any)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003

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

universe u

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem quantitative_separatingPositives_any
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hpert : UniformPerturbationOne_any A σ) :
    QuantitativeSeparatingPositives A σ := by
  sorry

end

end

end WeakPureInfiniteness
end

end OAI
end
