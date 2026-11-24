-- Prove2me | Theorems.Thm_GlobalTheory_BI_subgroupFunctionExtendByZero_conj_of_mem
-- name    : GlobalTheory.BI.subgroupFunctionExtendByZero_conj_of_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:44.419811+00:00
-- url     : https://prove2.me/theorems/157f230c-8655-4f81-894c-bd8b181c936f
-- title:
--   BI: subgroup Function Extend By Zero conj of mem
-- statement:
--   The BI construction uses the subgroup Function Extend By Zero conj of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InducedClassFunctionFromSubgroupEqFinsumCosets.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InducedClassFunctionFromSubgroupEqFinsumCosets.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.subgroupFunctionExtendByZero_conj_of_mem {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L)
    (hψ : ∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) (a : G) (y : H) :
    ext0 H ψ ((y : G)⁻¹ * a * y) = ext0 H ψ a := by sorry
