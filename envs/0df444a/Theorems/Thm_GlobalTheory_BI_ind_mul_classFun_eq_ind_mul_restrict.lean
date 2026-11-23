-- Prove2me | Theorems.Thm_GlobalTheory_BI_ind_mul_classFun_eq_ind_mul_restrict
-- name    : GlobalTheory.BI.ind_mul_classFun_eq_ind_mul_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:27.15503+00:00
-- url     : https://prove2.me/theorems/1f972d33-2f77-4681-82b5-c6d830e2284f
-- title:
--   BI: ind mul class Fun eq ind mul restrict
-- statement:
--   The BI construction uses the ind mul class Fun eq ind mul restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndMulClassFunEqIndMulRestrict.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndMulClassFunEqIndMulRestrict.lean#L9-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndMulClassFunEqIndMulRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.ind_mul_classFun_eq_ind_mul_restrict :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → ℂ) (φ : G → ℂ),
      (∀ g x : G, φ (x⁻¹ * g * x) = φ g) → ind H ψ * φ = ind H (fun h => ψ h * φ h) := by sorry
