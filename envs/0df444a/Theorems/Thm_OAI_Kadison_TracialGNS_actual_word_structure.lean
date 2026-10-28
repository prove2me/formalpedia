-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_actual_word_structure
-- name    : OAI.Kadison.TracialGNS.actual_word_structure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:55:34.579869+00:00
-- url     : https://prove2.me/theorems/ae30ecc3-2ea0-4601-8eeb-814d31c7413c
-- title:
--   OAI.Kadison.TracialGNS.actual_word_structure: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open scoped InnerProductSpace TensorProduct ComplexOrder`, `open UniformSpace`, `open scoped InnerProductSpace _root_.Topology`, `open scoped TensorProduct`, `open UniformSpace`, `open scoped TensorProduct InnerProductSpace`, `open scoped InnerProductSpace ENNReal`, `open ContinuousLinearMap`, `open scoped InnerProductSpace ENNReal`, `open scoped ComplexOrder InnerProductSpace TensorProduct`, `open UniformSpace ContinuousLinearMap`, `open PreHilbert HilbertTensor`):
--
--   ```lean
--   theorem actual_word_structure : ∃ B : ∀ k, J k →L[ℂ] J k,
--       (∀ k, ‖B k‖ ≤ ‖G‖) ∧
--       (∀ k (d : fullSpace τ) (x : zeroSpace τ) (a : J k),
--         G (U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a)) =
--           U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B k a))) ∧
--       (∀ k (d : fullSpace τ) (x : zeroSpace τ) (a : J k),
--         G.adjoint (U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a)) =
--           U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) ((B k).adjoint a)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power`, `OAI.Kadison.PreHilbert.word` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.HilbertTensor.pair` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialGNS.stageAlgebra` and `OAI.Kadison.TracialGNS.stageUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.TracialGNS.fullSpace` (definitions bundle `OAIQ039C040` of this split); `OAI.Kadison.TracialGNS.zeroSpace` (definitions bundle `OAIQ039C048` of this split); `OAI.Kadison.TracialGNS.sumLevel` (definitions bundle `OAIQ039C057` of this split); `OAI.Kadison.TracialGNS.sumLevelNormed` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.TracialGNS.sumLeft` (definitions bundle `OAIQ039C066` of this split); `OAI.Kadison.TracialGNS.sumConjugation` and `OAI.Kadison.TracialGNS.sumLevelInner` (definitions bundle `OAIQ039C067` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.free_word_structure` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C066
import Definitions.Def_OAIQ039C067

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
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

variable (J : ℕ → Type*) [∀ k, NormedAddCommGroup (J k)]
  [∀ k, InnerProductSpace ℂ (J k)] [∀ k, CompleteSpace (J k)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : ∀ k, sumLevel τ J k →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ (sumLevel τ J) U)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈ Set.centralizer (Set.centralizer
  (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))))

variable (L : A → H →L[ℂ] H)

variable (W : ∀ n, unitary (Matrix (I n) (I n) ℂ) → H →L[ℂ] H)

variable (hL : ∀ a k, (L a).comp (U k).toContinuousLinearMap =
  (U k).toContinuousLinearMap.comp (sumLeft τ J a k))

variable (hW : ∀ n u k, (W n u).comp (U k).toContinuousLinearMap =
  (U k).toContinuousLinearMap.comp
    (sumConjugation τ hτ J (stageUnitary (φ n) u) k))

variable (G : H →L[ℂ] H)

variable (hGL : ∀ a, G.comp (L a)=(L a).comp G)

variable (hGW : ∀ n u, G.comp (W n u)=(W n u).comp G)

include h1 hU he hsize hgen hL hW hGL hGW in
theorem actual_word_structure : ∃ B : ∀ k, J k →L[ℂ] J k,
    (∀ k, ‖B k‖ ≤ ‖G‖) ∧
    (∀ k (d : fullSpace τ) (x : zeroSpace τ) (a : J k),
      G (U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a)) =
        U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B k a))) ∧
    (∀ k (d : fullSpace τ) (x : zeroSpace τ) (a : J k),
      G.adjoint (U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a)) =
        U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) ((B k).adjoint a))) := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
