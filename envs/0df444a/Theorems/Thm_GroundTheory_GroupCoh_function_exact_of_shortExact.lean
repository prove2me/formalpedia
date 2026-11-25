-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_function_exact_of_shortExact
-- name    : GroundTheory.GroupCoh.function_exact_of_shortExact
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:32:23.209238+00:00
-- url     : https://prove2.me/theorems/69d93d44-9465-4f78-b0e7-c23366b6244a
-- title:
--   Group Coh: function exact of short Exact
-- statement:
--   The Group Coh construction uses the function exact of short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L143-L147

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

theorem GroundTheory.GroupCoh.function_exact_of_shortExact {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) :
    Function.Exact S.f.hom.toLinearMap S.g.hom.toLinearMap := by sorry
