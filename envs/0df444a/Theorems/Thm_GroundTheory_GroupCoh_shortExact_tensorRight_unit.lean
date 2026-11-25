-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_shortExact_tensorRight_unit
-- name    : GroundTheory.GroupCoh.shortExact_tensorRight_unit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:04.306815+00:00
-- url     : https://prove2.me/theorems/2f5e91ca-cc08-4c8f-80c3-bc6b6c9ec7a5
-- title:
--   Group Coh: short Exact tensor Right unit
-- statement:
--   The Group Coh construction uses the short Exact tensor Right unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateCupUnit
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
variable (E : ShortComplex (Rep.{u} k G))
variable {E}

theorem GroundTheory.GroupCoh.shortExact_tensorRight_unit (hE : E.ShortExact) :
    (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact := by sorry
