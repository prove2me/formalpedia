-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_range_repSubOne
-- name    : GroundTheory.GroupCoh.range_repSubOne
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:13.485941+00:00
-- url     : https://prove2.me/theorems/2e5796d4-0fe6-4099-a531-db040058219c
-- title:
--   Group Coh: range rep Sub One
-- statement:
--   The Group Coh construction uses the range rep Sub One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean#L26-L31

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandRep
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_HerbrandTate
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
universe u
open CategoryTheory
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.range_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).range = (Representation.Coinvariants.ker A.ρ).toAddSubgroup := by sorry
