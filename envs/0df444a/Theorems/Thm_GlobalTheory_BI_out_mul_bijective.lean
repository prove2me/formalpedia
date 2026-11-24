-- Prove2me | Theorems.Thm_GlobalTheory_BI_out_mul_bijective
-- name    : GlobalTheory.BI.out_mul_bijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:31.633886+00:00
-- url     : https://prove2.me/theorems/e7e38f45-5192-484b-bebc-8717741d2582
-- title:
--   BI: out mul bijective
-- statement:
--   The BI construction uses the out mul bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InducedClassFunctionFromSubgroupEqFinsumCosets.lean#L24-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InducedClassFunctionFromSubgroupEqFinsumCosets.lean#L24-L40

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

theorem GlobalTheory.BI.out_mul_bijective {G : Type} [Group G] (H : Subgroup G) :
    Function.Bijective (fun p : (G ⧸ H) × H => p.1.out * (p.2 : G)) := by sorry
