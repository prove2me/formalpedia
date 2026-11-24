-- Prove2me | Theorems.Thm_GlobalTheory_BI_out_conj_mem_iff_smul_eq
-- name    : GlobalTheory.BI.out_conj_mem_iff_smul_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:44.933432+00:00
-- url     : https://prove2.me/theorems/f354bffb-1d4d-4c7a-8d4d-46505559a306
-- title:
--   BI: out conj mem iff smul eq
-- statement:
--   The BI construction uses the out conj mem iff smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndRestrictEqCardFixedByMul.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndRestrictEqCardFixedByMul.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndRestrictEqCardFixedByMul
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

theorem GlobalTheory.BI.out_conj_mem_iff_smul_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    q.out⁻¹ * g * q.out ∈ H ↔ g • q = q := by sorry
