-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_partialProd_last_revInv
-- name    : GroundTheory.GroupCoh.partialProd_last_revInv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:57.967549+00:00
-- url     : https://prove2.me/theorems/6e9c74dc-2555-4898-9057-974864437ebd
-- title:
--   Group Coh: partial Prod last rev Inv
-- statement:
--   The Group Coh construction uses the partial Prod last rev Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CochainReverse.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CochainReverse.lean#L45-L61

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {G : Type*} [Group G] {n : ℕ}

theorem GroundTheory.GroupCoh.partialProd_last_revInv (x : Fin n → G) :
    Fin.partialProd (revInv x) (Fin.last n) = (Fin.partialProd x (Fin.last n))⁻¹ := by sorry
