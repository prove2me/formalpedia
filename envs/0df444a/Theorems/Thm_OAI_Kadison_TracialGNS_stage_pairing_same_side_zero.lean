-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_stage_pairing_same_side_zero
-- name    : OAI.Kadison.TracialGNS.stage_pairing_same_side_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:32:02.911069+00:00
-- url     : https://prove2.me/theorems/79ff7a1c-70f1-4f6f-aa30-2de6615fc53b
-- title:
--   OAI.Kadison.TracialGNS.stage_pairing_same_side_zero: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open PreHilbert`):
--
--   ```lean
--   theorem stage_pairing_same_side_zero (Is : ℕ → Type*)
--       [∀ n, Fintype (Is n)] [∀ n, DecidableEq (Is n)] [∀ n, Nonempty (Is n)]
--       (φs : ∀ n, Matrix (Is n) (Is n) ℂ →⋆ₐ[ℂ] A)
--       (hsize : ∀ q : ℕ, ∃ n, q ≤ Fintype.card (Is n))
--       (c : Pairing (TailSlots k l) → ℂ)
--       (hexp : ∀ n (v : TailSlots k l → Matrix (Is n) (Is n) ℂ),
--         (∀ j, Matrix.trace (v j) = 0) →
--         stageCoefficient τ Y (φs n) (fun o => o.elim (1 : Matrix (Is n) (Is n) ℂ) v) =
--           ∑ σ, c σ * Pairing.contraction σ
--             (fun X Z => (Fintype.card (Is n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v)
--       (σ : Pairing (TailSlots k l))
--       (hsame : (∃ a b : Fin k, σ (.inl a) = .inl b) ∨
--         (∃ a b : Fin l, σ (.inr a) = .inr b)) : c σ = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TailSlots` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.Pairing`, `OAI.Kadison.Pairing.contraction` and `OAI.Kadison.Pairing.instFintype` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.TracialGNS.fullSpace` (definitions bundle `OAIQ039C040` of this split); `OAI.Kadison.TracialGNS.zeroSpace` (definitions bundle `OAIQ039C048` of this split); `OAI.Kadison.TracialGNS.stageCoefficient` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.stageCoefficient_crossing` of this split imports it.
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

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {k l : ℕ} (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

include hτ h1 in
theorem stage_pairing_same_side_zero (Is : ℕ → Type*)
    [∀ n, Fintype (Is n)] [∀ n, DecidableEq (Is n)] [∀ n, Nonempty (Is n)]
    (φs : ∀ n, Matrix (Is n) (Is n) ℂ →⋆ₐ[ℂ] A)
    (hsize : ∀ q : ℕ, ∃ n, q ≤ Fintype.card (Is n))
    (c : Pairing (TailSlots k l) → ℂ)
    (hexp : ∀ n (v : TailSlots k l → Matrix (Is n) (Is n) ℂ),
      (∀ j, Matrix.trace (v j) = 0) →
      stageCoefficient τ Y (φs n) (fun o => o.elim (1 : Matrix (Is n) (Is n) ℂ) v) =
        ∑ σ, c σ * Pairing.contraction σ
          (fun X Z => (Fintype.card (Is n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v)
    (σ : Pairing (TailSlots k l))
    (hsame : (∃ a b : Fin k, σ (.inl a) = .inl b) ∨
      (∃ a b : Fin l, σ (.inr a) = .inr b)) : c σ = 0 := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
