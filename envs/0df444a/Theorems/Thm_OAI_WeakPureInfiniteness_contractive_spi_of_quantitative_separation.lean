-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_contractive_spi_of_quantitative_separation
-- name    : OAI.WeakPureInfiniteness.contractive_spi_of_quantitative_separation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:21:32.260316+00:00
-- url     : https://prove2.me/theorems/58aa4da8-1195-475c-8e32-b5842e6fc153
-- title:
--   OAI.WeakPureInfiniteness.contractive_spi_of_quantitative_separation: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.contractive_spi_of_quantitative_separation` of [lean/OAI/Analysis/WeakInfiniteness/QuantitativeAssembly.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/QuantitativeAssembly.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open scoped Topology CStarAlgebra`):
--
--   ```lean
--   theorem contractive_spi_of_quantitative_separation
--       (hpi : ∀ x : A,0 ≤ x → ProperlyInfinite (diagonalCopies 1 x))
--       {σ : ℝ} (hσ : 0 < σ) (hsep : QuantitativeSeparatingPositives A σ)
--       (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) (han : ‖a‖ ≤ 1) (hbn : ‖b‖ ≤ 1)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ s t : A, ‖star s*(a*a)*s-a*a‖ < ε ∧
--         ‖star t*(b*b)*t-b*b‖ < ε ∧ ‖star s*a*b*t‖ < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.QuantitativeSeparatingPositives` (definitions bundle `OAIQ246W003` of this split); `OAI.WeakPureInfiniteness.ProperlyInfinite` and `OAI.WeakPureInfiniteness.diagonalCopies` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/QuantitativeAssembly.lean (declaration OAI.WeakPureInfiniteness.contractive_spi_of_quantitative_separation)

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

noncomputable section

open scoped Topology CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem contractive_spi_of_quantitative_separation
    (hpi : ∀ x : A,0 ≤ x → ProperlyInfinite (diagonalCopies 1 x))
    {σ : ℝ} (hσ : 0 < σ) (hsep : QuantitativeSeparatingPositives A σ)
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) (han : ‖a‖ ≤ 1) (hbn : ‖b‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s t : A, ‖star s*(a*a)*s-a*a‖ < ε ∧
      ‖star t*(b*b)*t-b*b‖ < ε ∧ ‖star s*a*b*t‖ < ε := by
  sorry

end

end WeakPureInfiniteness
end

end OAI
end
