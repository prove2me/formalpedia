-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_cnt_zero
-- name    : GlobalTheory.Mem.RayData.cnt_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:59.21636+00:00
-- url     : https://prove2.me/theorems/03a1e430-7aaa-4f7f-9235-084f865151ed
-- title:
--   Ray Data: cnt zero
-- statement:
--   The Ray Data construction uses the cnt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L297-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L297-L301

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

theorem GlobalTheory.Mem.RayData.cnt_zero (hM : 2 ≤ M) (c : D.G) : D.cnt c 0 = 0 := by sorry
