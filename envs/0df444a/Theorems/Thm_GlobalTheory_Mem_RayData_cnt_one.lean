-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_cnt_one
-- name    : GlobalTheory.Mem.RayData.cnt_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:52.413983+00:00
-- url     : https://prove2.me/theorems/19d16b8d-4bad-4e4e-a832-2fc2ec196733
-- title:
--   Ray Data: cnt one
-- statement:
--   The Ray Data construction uses the cnt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L305-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L305-L320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
open Classical

theorem GlobalTheory.Mem.RayData.cnt_one (c : D.G) : D.cnt c 1 = if c = 1 then 1 else 0 := by sorry
