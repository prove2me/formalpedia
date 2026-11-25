-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_isAdj_U
-- name    : GlobalTheory.LatPair.Model.isAdj_U
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:44.33402+00:00
-- url     : https://prove2.me/theorems/621c7489-3602-5fde-9af5-6bf1c621ed9f
-- title:
--   Model: is Adj U
-- statement:
--   The Model construction uses the is Adj U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L51-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
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
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

theorem GlobalTheory.LatPair.Model.isAdj_U (q : Unif k) : IsAdj (U q : Module.End ℂ (Form k n ℂ)) (D q) := by sorry
