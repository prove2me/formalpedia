-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_revHom_naturality
-- name    : GroundTheory.GroupCoh.revHom_naturality
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:32.031854+00:00
-- url     : https://prove2.me/theorems/af6e68ff-f4c6-45d2-a06b-8599d286c1b1
-- title:
--   Group Coh: rev Hom naturality
-- statement:
--   The Group Coh construction uses the rev Hom naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CochainReverse.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CochainReverse.lean#L193-L198

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
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G)
variable {A}

theorem GroundTheory.GroupCoh.revHom_naturality {B : Rep k G} (φ : A ⟶ B) :
    revHom A ≫ cochainsMap (MonoidHom.id G) φ = cochainsMap (MonoidHom.id G) φ ≫ revHom B := by sorry
