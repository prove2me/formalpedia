-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_sq_comp
-- name    : GroundTheory.GroupCoh.sq_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:08:17.687071+00:00
-- url     : https://prove2.me/theorems/efa255f5-8281-5f63-bdda-68f21291dc7a
-- title:
--   Group Coh: sq comp
-- statement:
--   The Group Coh construction uses the sq comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L25-L28

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

theorem GroundTheory.GroupCoh.sq_comp {C : Type*} [Category C] {a₁ a₂ a₃ b₁ b₂ b₃ : C} {δ₁ : a₁ ⟶ b₁} {δ₂ : a₂ ⟶ b₂}
    {δ₃ : a₃ ⟶ b₃} {f : b₁ ⟶ b₂} {f' : a₁ ⟶ a₂} {g : b₂ ⟶ b₃} {g' : a₂ ⟶ a₃}
    (h₁ : δ₁ ≫ f = f' ≫ δ₂) (h₂ : δ₂ ≫ g = g' ≫ δ₃) : δ₁ ≫ (f ≫ g) = (f' ≫ g') ≫ δ₃ := by sorry
