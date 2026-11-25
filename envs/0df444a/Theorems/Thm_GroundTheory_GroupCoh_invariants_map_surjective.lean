-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_invariants_map_surjective
-- name    : GroundTheory.GroupCoh.invariants_map_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:53.106111+00:00
-- url     : https://prove2.me/theorems/ccc55eb0-8e3f-4242-90d4-8d5d29cee892
-- title:
--   Group Coh: invariants map surjective
-- statement:
--   The Group Coh construction uses the invariants map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L48-L57

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
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
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]

theorem GroundTheory.GroupCoh.invariants_map_surjective {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (h1 : IsZero (groupCohomology X.X₁ 1)) :
    Function.Surjective ((invariantsFunctor k G).map X.g).hom := by sorry
