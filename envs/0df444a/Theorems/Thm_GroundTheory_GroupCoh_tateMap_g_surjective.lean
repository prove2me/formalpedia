-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateMap_g_surjective
-- name    : GroundTheory.GroupCoh.tateMap_g_surjective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:29.721179+00:00
-- url     : https://prove2.me/theorems/e6d713f5-822f-4cea-a2d2-89a3971600ce
-- title:
--   Group Coh: tate Map g surjective
-- statement:
--   The Group Coh construction uses the tate Map g surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L164-L167

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable {X Y Z : Rep k G}
variable {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
include hS

theorem GroundTheory.GroupCoh.tateMap_g_surjective (i : ℤ) : Function.Surjective ((tateComplex.map S.g).f i).hom := by sorry
