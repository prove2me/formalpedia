-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Pair_hasVal_ev
-- name    : GlobalTheory.LatPair.Pair.hasVal_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:52.030327+00:00
-- url     : https://prove2.me/theorems/7e3091fe-1361-4e11-a893-9624e16bbe31
-- title:
--   Pair: has Val ev
-- statement:
--   The Pair construction uses the has Val ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L313-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L313-L313

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
open GlobalTheory.LatPair.Pair

theorem GlobalTheory.LatPair.Pair.hasVal_ev {P : Pair k n} {x : n → k} (h : x ∈ P.lat) : P.HasVal x (P.ev x) := by sorry
