-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_cls_mul_of_two_le
-- name    : GlobalTheory.Mem.RayData.cls_mul_of_two_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:17.093797+00:00
-- url     : https://prove2.me/theorems/21d2cd86-4b9b-4f62-b3e7-b327b1f1d16b
-- title:
--   Ray Data: cls mul of two le
-- statement:
--   The Ray Data construction uses the cls mul of two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L226-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L226-L227

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

theorem GlobalTheory.Mem.RayData.cls_mul_of_two_le (hM : 2 ≤ M) {I J : Ideal (𝓞 K)} (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)}))
    (hJ : IsCoprime J (Ideal.span {(M : 𝓞 K)})) : D.cls (I * J) = D.cls I * D.cls J := by sorry
