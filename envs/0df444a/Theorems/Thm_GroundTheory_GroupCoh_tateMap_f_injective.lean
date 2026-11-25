-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateMap_f_injective
-- name    : GroundTheory.GroupCoh.tateMap_f_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:21.902421+00:00
-- url     : https://prove2.me/theorems/458f0852-3eed-4542-b6d6-0739ffe0d9c2
-- title:
--   Group Coh: tate Map f injective
-- statement:
--   The Group Coh construction uses the tate Map f injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L169-L172

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

theorem GroundTheory.GroupCoh.tateMap_f_injective (i : ℤ) : Function.Injective ((tateComplex.map S.f).f i).hom := by sorry
