-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_sq_sum
-- name    : GroundTheory.GroupCoh.sq_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:38.0958+00:00
-- url     : https://prove2.me/theorems/b0abc695-f595-4382-bc15-025073215ea8
-- title:
--   Group Coh: sq sum
-- statement:
--   The Group Coh construction uses the sq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L30-L34

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

theorem GroundTheory.GroupCoh.sq_sum {C : Type*} [Category C] [Preadditive C] {a₁ a₂ b₁ b₂ : C} {δ₁ : a₁ ⟶ b₁}
    {δ₂ : a₂ ⟶ b₂} {ι : Type*} (s : Finset ι) {f : ι → (b₁ ⟶ b₂)} {f' : ι → (a₁ ⟶ a₂)}
    (h : ∀ i ∈ s, δ₁ ≫ f i = f' i ≫ δ₂) : δ₁ ≫ ∑ i ∈ s, f i = (∑ i ∈ s, f' i) ≫ δ₂ := by sorry
