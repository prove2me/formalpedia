-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_stageWord_inner_classification
-- name    : OAI.Kadison.TracialGNS.stageWord_inner_classification
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:31:39.643934+00:00
-- url     : https://prove2.me/theorems/185e91c6-e9ba-4292-a550-ae90c46a56f3
-- title:
--   OAI.Kadison.TracialGNS.stageWord_inner_classification: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open PreHilbert UniformSpace`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem stageWord_inner_classification (I : ℕ → Type*)
--       [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
--       (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
--       (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
--       (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
--       (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
--       (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
--         Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
--           (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
--       (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
--       ∃ c₀ : (Fin k ≃ Fin l) → ℂ, ∀ n (d c : Matrix (I n) (I n) ℂ)
--         (x : Fin k → Matrix (I n) (I n) ℂ) (y : Fin l → Matrix (I n) (I n) ℂ),
--         (∀ i, Matrix.trace (x i) = 0) → (∀ j, Matrix.trace (y j) = 0) →
--         inner ℂ (word (fullSpace τ) (zeroSpace τ) l (stageVector τ (φ n) c)
--           (fun j => centeredStageVector τ (φ n) (y j)))
--           (Y (word (fullSpace τ) (zeroSpace τ) k (stageVector τ (φ n) d)
--             (fun i => centeredStageVector τ (φ n) (x i)))) =
--         inner ℂ (stageVector τ (φ n) c) (stageVector τ (φ n) d) *
--           ∑ b : Fin k ≃ Fin l, c₀ b * ∏ i,
--             inner ℂ (centeredStageVector τ (φ n) (y (b i)))
--               (centeredStageVector τ (φ n) (x i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.vacuum` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power`, `OAI.Kadison.PreHilbert.word` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.centeredSpace` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.TracialGNS.stageUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.TracialGNS.stageVector` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.TracialGNS.fullSpace` (definitions bundle `OAIQ039C040` of this split); `OAI.Kadison.TracialGNS.zeroSpace` (definitions bundle `OAIQ039C048` of this split); `OAI.Kadison.TracialGNS.centeredStageVector` (definitions bundle `OAIQ039C052` of this split); `OAI.Kadison.TracialGNS.wordConjugation` and `OAI.Kadison.TracialGNS.wordLeft` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.word_multiplicity_slices` of this split imports it.
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

open PreHilbert UniformSpace

open scoped TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

include hτ h1 in
theorem stageWord_inner_classification (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c₀ : (Fin k ≃ Fin l) → ℂ, ∀ n (d c : Matrix (I n) (I n) ℂ)
      (x : Fin k → Matrix (I n) (I n) ℂ) (y : Fin l → Matrix (I n) (I n) ℂ),
      (∀ i, Matrix.trace (x i) = 0) → (∀ j, Matrix.trace (y j) = 0) →
      inner ℂ (word (fullSpace τ) (zeroSpace τ) l (stageVector τ (φ n) c)
        (fun j => centeredStageVector τ (φ n) (y j)))
        (Y (word (fullSpace τ) (zeroSpace τ) k (stageVector τ (φ n) d)
          (fun i => centeredStageVector τ (φ n) (x i)))) =
      inner ℂ (stageVector τ (φ n) c) (stageVector τ (φ n) d) *
        ∑ b : Fin k ≃ Fin l, c₀ b * ∏ i,
          inner ℂ (centeredStageVector τ (φ n) (y (b i)))
            (centeredStageVector τ (φ n) (x i)) := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
