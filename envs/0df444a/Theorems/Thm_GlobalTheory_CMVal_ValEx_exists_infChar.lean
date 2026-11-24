-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_infChar
-- name    : GlobalTheory.CMVal.ValEx.exists_infChar
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:28.292624+00:00
-- url     : https://prove2.me/theorems/334ba1e9-a13d-4d3f-b9bd-4a7d0508da44
-- title:
--   Val Ex: exists inf Char
-- statement:
--   The Val Ex construction uses the exists inf Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L277-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L277-L308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.ValEx.exists_infChar {I : Type} [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) :
    ∃ ψ : (InfiniteAdeleRing E)ˣ →* ℂˣ, Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ k : Eˣ, ((ψ (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) : ℂˣ) : ℂ) =
        ∏ i, (φ i (k : E) / starRingEnd ℂ (φ i (k : E))) ^ m i) ∧
      ∀ k : E, k ∈ maximalRealSubfield E → ∀ x : (InfiniteAdeleRing E)ˣ,
        (∀ w, x.1 w = (1 : InfiniteAdeleRing E) w ∨ x.1 w = algebraMap E (InfiniteAdeleRing E) k w) → ψ x = 1 := by sorry
