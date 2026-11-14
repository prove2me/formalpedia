-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_exists_uniform_reducing_model
-- name    : OAI.WeakPureInfiniteness.exists_uniform_reducing_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:15:28.794642+00:00
-- url     : https://prove2.me/theorems/91617bc9-c992-4426-8357-76a2133ab5c9
-- title:
--   OAI.WeakPureInfiniteness.exists_uniform_reducing_model: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.exists_uniform_reducing_model` of [lean/OAI/Analysis/WeakInfiniteness/FiniteReducingModels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/FiniteReducingModels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open scoped InnerProductSpace CStarAlgebra ComplexOrder`):
--
--   ```lean
--   theorem exists_uniform_reducing_model {n : ℕ} (hn : 1 ≤ n)
--       (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
--       (c : A) (hc : 0 ≤ c) {α : ℝ} (hα : 0 < α) (d : ℕ)
--       (D : CStarMatrix (Fin d) (Fin d) ℂ) (hD : ‖D‖ ≤ 1) :
--       ∃ w : CStarMatrix (Fin n) (Fin n) A, ‖w‖ ≤ 1 ∧
--         diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*w*
--           diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)=w ∧
--         ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
--           (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π c‖ →
--           ∃ J : HilbertVector (Fin d) ℂ →ₗᵢ[ℂ] HilbertVector (Fin n) H,
--             (matrixRepresentation π (Fin n) w).comp J.toContinuousLinearMap=
--               J.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D) ∧
--             (matrixRepresentation π (Fin n) w).adjoint.comp J.toContinuousLinearMap=
--               J.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D).adjoint
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.HilbertVector`, `OAI.WeakPureInfiniteness.matrixRepresentation`, `OAI.WeakPureInfiniteness.scalarMatrixAction` and `OAI.WeakPureInfiniteness.spectralRamp` (definitions bundle `OAIQ246W001` of this split); `OAI.WeakPureInfiniteness.ProperlyInfinite` and `OAI.WeakPureInfiniteness.diagonalCopies` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.exists_separated_supported_model_any` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/FiniteReducingModels.lean (declaration OAI.WeakPureInfiniteness.exists_uniform_reducing_model)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W001

section

attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
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

open scoped InnerProductSpace CStarAlgebra ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_uniform_reducing_model {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (c : A) (hc : 0 ≤ c) {α : ℝ} (hα : 0 < α) (d : ℕ)
    (D : CStarMatrix (Fin d) (Fin d) ℂ) (hD : ‖D‖ ≤ 1) :
    ∃ w : CStarMatrix (Fin n) (Fin n) A, ‖w‖ ≤ 1 ∧
      diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*w*
        diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)=w ∧
      ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π c‖ →
        ∃ J : HilbertVector (Fin d) ℂ →ₗᵢ[ℂ] HilbertVector (Fin n) H,
          (matrixRepresentation π (Fin n) w).comp J.toContinuousLinearMap=
            J.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D) ∧
          (matrixRepresentation π (Fin n) w).adjoint.comp J.toContinuousLinearMap=
            J.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D).adjoint := by
  sorry

end

end WeakPureInfiniteness
end

end OAI
end
