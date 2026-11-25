-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_subfieldInfinitePlaceEquiv_mk
-- name    : GroundTheory.Global.Artin.subfieldInfinitePlaceEquiv_mk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:56:16.257708+00:00
-- url     : https://prove2.me/theorems/7a2dbfd3-8503-5692-9857-73ab3f151acd
-- title:
--   Artin: subfield Infinite Place Equiv mk
-- statement:
--   The Artin construction uses the subfield Infinite Place Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesInfinite.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesInfinite.lean#L111-L114

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
variable (w : InfinitePlace L)

theorem GroundTheory.Global.Artin.subfieldInfinitePlaceEquiv_mk (x : Gal(L/K)) :
    (subfieldInfinitePlaceEquiv H w (DoubleCoset.mk _ _ x) : InfinitePlace (fixedField H)) =
      subfieldInfinitePlace H w x := by sorry

attribute [defeq] GroundTheory.Global.Artin.subfieldInfinitePlaceEquiv_mk
