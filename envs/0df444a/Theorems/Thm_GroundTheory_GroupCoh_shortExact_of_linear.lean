-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_shortExact_of_linear
-- name    : GroundTheory.GroupCoh.shortExact_of_linear
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:39.565842+00:00
-- url     : https://prove2.me/theorems/4ef76b72-e9ec-422f-8896-752f6885f6ab
-- title:
--   Group Coh: short Exact of linear
-- statement:
--   The Group Coh construction uses the short Exact of linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L17-L25

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

theorem GroundTheory.GroupCoh.shortExact_of_linear {S : ShortComplex (Rep.{u} k G)} (hf : Function.Injective S.f.hom)
    (hg : Function.Surjective S.g.hom) (h : ∀ y : S.X₂, S.g.hom y = 0 → ∃ x, S.f.hom x = y) :
    S.ShortExact := by sorry
