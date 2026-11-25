-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_cross_up
-- name    : GlobalTheory.LatPair.cross_up
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:10.053988+00:00
-- url     : https://prove2.me/theorems/298b02c3-df7d-4128-86b7-c670064e26d2
-- title:
--   Lat Pair: cross up
-- statement:
--   The Lat Pair construction uses the cross up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L493-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L493-L497

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}

theorem GlobalTheory.LatPair.cross_up (q : Unif k) (P : Pair k n) (x : {x : Red P.lat // x ≠ 0}) :
    cross q (up P.lat q x) P = P.red x.1 := by sorry
