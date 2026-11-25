-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_shortExact_map_tensorLeft
-- name    : GroundTheory.GroupCoh.shortExact_map_tensorLeft
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:32:15.010642+00:00
-- url     : https://prove2.me/theorems/4b6c37a9-927a-4a34-a544-847e55589d69
-- title:
--   Group Coh: short Exact map tensor Left
-- statement:
--   The Group Coh construction uses the short Exact map tensor Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L162-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L162-L173

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

theorem GroundTheory.GroupCoh.shortExact_map_tensorLeft {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (Y : Rep.{u} k G) (hinj : Function.Injective (Y ◁ S.f).hom) :
    (S.map (tensorLeft Y)).ShortExact := by sorry
