-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_isAdj_FF
-- name    : GlobalTheory.LatPair.Model.isAdj_FF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:49.881977+00:00
-- url     : https://prove2.me/theorems/a7c55b19-ccb9-5db4-923f-de8db1944e84
-- title:
--   Model: is Adj FF
-- statement:
--   The Model construction uses the is Adj FF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L47-L49

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

theorem GlobalTheory.LatPair.Model.isAdj_FF {ψ : AddChar k Circle} (hψ : SplitWeil.HasConductor ψ 1) (q : Unif k) :
    IsAdj (FF q (resChar ψ hψ q) : Module.End ℂ (Form k n ℂ)) (FFStar q (resChar ψ hψ q)) := by sorry
