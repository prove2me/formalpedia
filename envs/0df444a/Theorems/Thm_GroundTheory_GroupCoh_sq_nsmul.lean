-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_sq_nsmul
-- name    : GroundTheory.GroupCoh.sq_nsmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:28.294727+00:00
-- url     : https://prove2.me/theorems/dc95449d-0b60-4e61-8bcd-1614a00115dc
-- title:
--   Group Coh: sq nsmul
-- statement:
--   The Group Coh construction uses the sq nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L36-L39

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]

theorem GroundTheory.GroupCoh.sq_nsmul {C : Type*} [Category C] [Preadditive C] {a₁ a₂ b₁ b₂ : C} {δ₁ : a₁ ⟶ b₁}
    {δ₂ : a₂ ⟶ b₂} (m : ℕ) {f : b₁ ⟶ b₂} {f' : a₁ ⟶ a₂} (h : δ₁ ≫ f = f' ≫ δ₂) :
    δ₁ ≫ (m • f) = (m • f') ≫ δ₂ := by sorry
