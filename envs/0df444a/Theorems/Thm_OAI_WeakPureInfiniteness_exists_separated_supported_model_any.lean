-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_exists_separated_supported_model_any
-- name    : OAI.WeakPureInfiniteness.exists_separated_supported_model_any
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:20:04.250106+00:00
-- url     : https://prove2.me/theorems/1d12b2de-0d8f-4e19-8939-71ad10555823
-- title:
--   OAI.WeakPureInfiniteness.exists_separated_supported_model_any: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.exists_separated_supported_model_any` of [lean/OAI/Analysis/WeakInfiniteness/CrossUniverseSupportedSeparation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/CrossUniverseSupportedSeparation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder`):
--
--   ```lean
--   theorem exists_separated_supported_model_any
--       {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
--       (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
--         ¬ FiniteContractionModelsAny B v γ)
--       (hA : Exact A) (hn : 1 ≤ n)
--       (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
--       (c : A) (hc : 0 ≤ c) {α : ℝ} (hα : 0 < α)
--       (e : CStarMatrix (Fin n) (Fin n) A) (he : IsSelfAdjoint e)
--       (U : CStarMatrix (Fin 1) (Fin n) A) (hU : U.conjTranspose*U=e)
--       (V : supportedAlgebra e he) :
--       ∃ w : CStarMatrix (Fin n) (Fin n) A, ‖w‖ ≤ 1 ∧
--         diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*w*
--           diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)=w ∧
--         ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
--           α ≤ ‖π c‖ → σ ≤ ‖matrixRepresentation π (Fin n) (V.val-w)‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.HilbertVector`, `OAI.WeakPureInfiniteness.matrixRepresentation`, `OAI.WeakPureInfiniteness.spectralRamp` and `OAI.WeakPureInfiniteness.supportedAlgebra` (definitions bundle `OAIQ246W001` of this split); `OAI.WeakPureInfiniteness.FiniteContractionModelsAny` (definitions bundle `OAIQ246W003` of this split); `OAI.WeakPureInfiniteness.ComplexHilbert`, `OAI.WeakPureInfiniteness.Exact`, `OAI.WeakPureInfiniteness.ProperlyInfinite` and `OAI.WeakPureInfiniteness.diagonalCopies` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proofs of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite` and `OAI.WeakPureInfiniteness.exists_finite_coupling_of_gap_any` of this split import it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/CrossUniverseSupportedSeparation.lean (declaration OAI.WeakPureInfiniteness.exists_separated_supported_model_any)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003

section

attribute [-instance] _root_.OAI.WeakPureInfiniteness.instIsClosedCoeNonUnitalStarSubalgebraComplexGeneratedClosedIdeal
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

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

theorem exists_separated_supported_model_any
    {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (c : A) (hc : 0 ≤ c) {α : ℝ} (hα : 0 < α)
    (e : CStarMatrix (Fin n) (Fin n) A) (he : IsSelfAdjoint e)
    (U : CStarMatrix (Fin 1) (Fin n) A) (hU : U.conjTranspose*U=e)
    (V : supportedAlgebra e he) :
    ∃ w : CStarMatrix (Fin n) (Fin n) A, ‖w‖ ≤ 1 ∧
      diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*w*
        diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)=w ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π c‖ → σ ≤ ‖matrixRepresentation π (Fin n) (V.val-w)‖ := by
  sorry

end

end WeakPureInfiniteness
end

end OAI
end
