-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_ker_repSubOne
-- name    : GroundTheory.GroupCoh.ker_repSubOne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:52.781214+00:00
-- url     : https://prove2.me/theorems/98e05e40-550a-4e57-9bc7-0fc5e3ac4a98
-- title:
--   Group Coh: ker rep Sub One
-- statement:
--   The Group Coh construction uses the ker rep Sub One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean#L20-L24

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
omit [Fintype G]

theorem GroundTheory.GroupCoh.ker_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).ker = A.ρ.invariants.toAddSubgroup := by sorry
