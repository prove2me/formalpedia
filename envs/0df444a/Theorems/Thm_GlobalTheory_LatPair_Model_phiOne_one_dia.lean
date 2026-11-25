-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_phiOne_one_dia
-- name    : GlobalTheory.LatPair.Model.phiOne_one_dia
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:07.51021+00:00
-- url     : https://prove2.me/theorems/7aae2853-6eb0-4e96-9ff1-d81bf2f2a9d9
-- title:
--   Model: phi One one dia
-- statement:
--   The Model construction uses the phi One one dia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L207-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L207-L212

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.LatPair.Model.phiOne_one_dia [Fintype n] [DecidableEq n] (P : Pair k n) {c : 𝓀[k]ˣ} (hc : c ≠ 1) :
    phiOne P (c • P) 1 = 0 := by sorry
