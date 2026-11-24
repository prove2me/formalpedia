-- Prove2me | Theorems.Thm_GlobalTheory_BI_inv_smul_eq_iff_conj_mem
-- name    : GlobalTheory.BI.inv_smul_eq_iff_conj_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:58:15.319294+00:00
-- url     : https://prove2.me/theorems/6c956ea1-a839-4e3a-a6d5-eba615863115
-- title:
--   BI: inv smul eq iff conj mem
-- statement:
--   The BI construction uses the inv smul eq iff conj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterFinsumConjSubgroupFunctionExtendByZer.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterFinsumConjSubgroupFunctionExtendByZer.lean#L56-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterFinsumConjSubgroupFunctionExtendByZer
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
variable {G : Type} [Group G] (H : Subgroup G)

theorem GlobalTheory.BI.inv_smul_eq_iff_conj_mem (g : G) (q : G ⧸ H) :
    g⁻¹ • q = q ↔ q.out⁻¹ * g * q.out ∈ H := by sorry
