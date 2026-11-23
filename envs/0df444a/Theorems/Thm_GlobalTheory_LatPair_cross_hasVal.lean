-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_cross_hasVal
-- name    : GlobalTheory.LatPair.cross_hasVal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:46.099715+00:00
-- url     : https://prove2.me/theorems/a1763971-f3b5-4305-85b1-5f6cd2f90d36
-- title:
--   Lat Pair: cross has Val
-- statement:
--   The Lat Pair construction uses the cross has Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L487-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L487-L491

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

theorem GlobalTheory.LatPair.cross_hasVal (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) {e : n → k} (he : P₁.HasVal e 1) :
    P.HasVal (q.1 • e) (cross q P₁ P) := by sorry
