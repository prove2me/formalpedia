-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_equivRayGroup_rcl
-- name    : GlobalTheory.Mem.RayData.equivRayGroup_rcl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:11.750963+00:00
-- url     : https://prove2.me/theorems/95245c7f-783a-4df6-87e7-70fb39c6e6b9
-- title:
--   Ray Data: equiv Ray Group rcl
-- statement:
--   The Ray Data construction uses the equiv Ray Group rcl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L277-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L277-L280

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

theorem GlobalTheory.Mem.RayData.equivRayGroup_rcl {I : Ideal (𝓞 K)} (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI' : I ≠ ⊥) :
    D.equivRayGroup (RayCl.rcl M I) = D.cls I := by sorry
