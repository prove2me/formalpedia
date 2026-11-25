-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Pair_HasVal_ev_eq
-- name    : GlobalTheory.LatPair.Pair.HasVal.ev_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:57.243998+00:00
-- url     : https://prove2.me/theorems/0e66d7d8-2d25-44d8-bc06-a317a25fcd6e
-- title:
--   Has Val: ev eq
-- statement:
--   The Has Val construction uses the ev eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L315-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L315-L316

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

theorem GlobalTheory.LatPair.Pair.HasVal.ev_eq {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) : P.ev x = a := by sorry
