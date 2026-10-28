-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_stage_pairing_expansion
-- name    : OAI.Kadison.TracialGNS.stage_pairing_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:31:38.630751+00:00
-- url     : https://prove2.me/theorems/42ad30c6-6be7-4842-b3a7-315ece2c16ef
-- title:
--   OAI.Kadison.TracialGNS.stage_pairing_expansion: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open PreHilbert`):
--
--   ```lean
--   lemma stage_pairing_expansion (d : Equiv.Perm (Option (TailSlots k l)) → ℂ)
--       (hd : ∀ σ, 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (TailSlots k l)) + 1 → d σ = 0)
--       (hexp : ∀ v : Option (TailSlots k l) → Matrix I I ℂ,
--         stageCoefficient τ Y φ v = ∑ σ, d σ * SchurWeyl.cycleTrace σ v)
--       (v : TailSlots k l → Matrix I I ℂ) (hv : ∀ j, Matrix.trace (v j) = 0) :
--       stageCoefficient τ Y φ (fun o => o.elim (1 : Matrix I I ℂ) v) =
--         ∑ σ : Pairing (TailSlots k l), d (SchurWeyl.endpointPairingPerm σ) *
--           Pairing.contraction σ (fun X Z => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Z)) v
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TailSlots` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.Pairing`, `OAI.Kadison.Pairing.contraction` and `OAI.Kadison.Pairing.instFintype` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.SchurWeyl.cycleCount`, `OAI.Kadison.SchurWeyl.cycleTrace` and `OAI.Kadison.SchurWeyl.endpointPairingPerm` (definitions bundle `OAIQ039C029` of this split); `OAI.Kadison.TracialGNS.fullSpace` (definitions bundle `OAIQ039C040` of this split); `OAI.Kadison.TracialGNS.zeroSpace` (definitions bundle `OAIQ039C048` of this split); `OAI.Kadison.TracialGNS.stageCoefficient` (definitions bundle `OAIQ039C058` of this split).
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

lemma stage_pairing_expansion (d : Equiv.Perm (Option (TailSlots k l)) → ℂ)
    (hd : ∀ σ, 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (TailSlots k l)) + 1 → d σ = 0)
    (hexp : ∀ v : Option (TailSlots k l) → Matrix I I ℂ,
      stageCoefficient τ Y φ v = ∑ σ, d σ * SchurWeyl.cycleTrace σ v)
    (v : TailSlots k l → Matrix I I ℂ) (hv : ∀ j, Matrix.trace (v j) = 0) :
    stageCoefficient τ Y φ (fun o => o.elim (1 : Matrix I I ℂ) v) =
      ∑ σ : Pairing (TailSlots k l), d (SchurWeyl.endpointPairingPerm σ) *
        Pairing.contraction σ (fun X Z => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Z)) v := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
