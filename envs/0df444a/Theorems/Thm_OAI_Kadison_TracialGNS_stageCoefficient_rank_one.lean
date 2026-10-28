-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_stageCoefficient_rank_one
-- name    : OAI.Kadison.TracialGNS.stageCoefficient_rank_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:31:22.389778+00:00
-- url     : https://prove2.me/theorems/83c61903-93ed-45a8-9130-41b98238c385
-- title:
--   OAI.Kadison.TracialGNS.stageCoefficient_rank_one: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open PreHilbert`):
--
--   ```lean
--   lemma stageCoefficient_rank_one (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
--       (hY : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y)
--       (b : Option (Fin k ⊕ Fin l) → I)
--       (σ : Equiv.Perm (Option (Fin k ⊕ Fin l))) :
--       ‖stageCoefficient τ Y φ (fun j => Matrix.single (b (σ j)) (b j) 1)‖ ≤
--         ‖Y‖ * (Fintype.card I : ℝ)⁻¹ *
--           (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ (Fintype.card (Option (Fin k ⊕ Fin l)) - 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialGNS.fullSpace` (definitions bundle `OAIQ039C040` of this split); `OAI.Kadison.TracialGNS.zeroSpace` (definitions bundle `OAIQ039C048` of this split); `OAI.Kadison.TracialGNS.stageCoefficient` and `OAI.Kadison.TracialGNS.wordLeft` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff` of this split imports it.
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

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

include hτ h1 in
lemma stageCoefficient_rank_one (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (hY : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y)
    (b : Option (Fin k ⊕ Fin l) → I)
    (σ : Equiv.Perm (Option (Fin k ⊕ Fin l))) :
    ‖stageCoefficient τ Y φ (fun j => Matrix.single (b (σ j)) (b j) 1)‖ ≤
      ‖Y‖ * (Fintype.card I : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ (Fintype.card (Option (Fin k ⊕ Fin l)) - 1) := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
