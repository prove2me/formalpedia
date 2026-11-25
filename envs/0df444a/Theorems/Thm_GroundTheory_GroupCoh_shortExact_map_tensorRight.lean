-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_shortExact_map_tensorRight
-- name    : GroundTheory.GroupCoh.shortExact_map_tensorRight
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:32:58.281499+00:00
-- url     : https://prove2.me/theorems/0328ab81-f35e-4a1d-95b1-d40131de03a4
-- title:
--   Group Coh: short Exact map tensor Right
-- statement:
--   The Group Coh construction uses the short Exact map tensor Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L149-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L149-L160

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
variable {A B : Rep.{u} k G}

theorem GroundTheory.GroupCoh.shortExact_map_tensorRight {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (Y : Rep.{u} k G) (hinj : Function.Injective (S.f ▷ Y).hom) :
    (S.map (tensorRight Y)).ShortExact := by sorry
