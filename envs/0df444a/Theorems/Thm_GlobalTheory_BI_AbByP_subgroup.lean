-- Prove2me | Theorems.Thm_GlobalTheory_BI_AbByP_subgroup
-- name    : GlobalTheory.BI.AbByP.subgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:49.232309+00:00
-- url     : https://prove2.me/theorems/42d39a14-d52b-4e82-a246-d99ae1e9ee89
-- title:
--   Ab By P: subgroup
-- statement:
--   The Ab By P construction uses the subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsAbelianByPrimePowerGroupSubgroup.lean#L5-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsAbelianByPrimePowerGroupSubgroup.lean#L5-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.AbByP.subgroup :
    ∀ (G : Type) [Group G] (T : Subgroup G),
      _root_.GlobalTheory.BI.AbByP G → _root_.GlobalTheory.BI.AbByP T := by sorry
