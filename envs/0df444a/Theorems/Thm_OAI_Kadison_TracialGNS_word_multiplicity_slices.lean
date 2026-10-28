-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_word_multiplicity_slices
-- name    : OAI.Kadison.TracialGNS.word_multiplicity_slices
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:32:34.552955+00:00
-- url     : https://prove2.me/theorems/04124cd5-3a51-4370-b4f4-1ed8117b9345
-- title:
--   OAI.Kadison.TracialGNS.word_multiplicity_slices: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open PreHilbert HilbertTensor`):
--
--   ```lean
--   theorem word_multiplicity_slices
--       (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
--         Completion (wordSpace (fullSpace τ) (zeroSpace τ) l ⊗[ℂ] K))
--       (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
--       (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
--       (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
--       (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
--       (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
--       (hd : Dense (⋃ n, stageSet τ I φ n))
--       (hT : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
--         T.comp (HilbertTensor.map (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap 1) =
--           (HilbertTensor.map (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap 1).comp T)
--       (hleft : ∀ a : A, T.comp (HilbertTensor.map (wordLeft τ a k) 1) =
--         (HilbertTensor.map (wordLeft τ a l) 1).comp T) :
--       ∀ a : J, ∀ b : K, ∃ c : (Fin k ≃ Fin l) → ℂ,
--         scalarSlice T a b = ∑ σ, c σ •
--           (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.HilbertTensor.map` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialGNS.stageUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.HilbertTensor.scalarSlice` (definitions bundle `OAIQ039C027` of this split); `OAI.Kadison.PreHilbert.wordReindex`, `OAI.Kadison.TracialGNS.fullSpace` and `OAI.Kadison.TracialGNS.stageSet` (definitions bundle `OAIQ039C040` of this split); `OAI.Kadison.TracialGNS.zeroSpace` (definitions bundle `OAIQ039C048` of this split); `OAI.Kadison.TracialGNS.wordConjugation` and `OAI.Kadison.TracialGNS.wordLeft` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.actual_word_structure` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C058

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable {k l : ℕ} {J K : Type*}
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

include h1 in
theorem word_multiplicity_slices
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) l ⊗[ℂ] K))
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hd : Dense (⋃ n, stageSet τ I φ n))
    (hT : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      T.comp (HilbertTensor.map (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap 1) =
        (HilbertTensor.map (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap 1).comp T)
    (hleft : ∀ a : A, T.comp (HilbertTensor.map (wordLeft τ a k) 1) =
      (HilbertTensor.map (wordLeft τ a l) 1).comp T) :
    ∀ a : J, ∀ b : K, ∃ c : (Fin k ≃ Fin l) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
