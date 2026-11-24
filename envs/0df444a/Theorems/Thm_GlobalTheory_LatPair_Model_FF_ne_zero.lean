-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_FF_ne_zero
-- name    : GlobalTheory.LatPair.Model.FF_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:53.208028+00:00
-- url     : https://prove2.me/theorems/d9d6cef0-13bb-4bd2-987c-849295c3479a
-- title:
--   Model: FF ne zero
-- statement:
--   The Model construction uses the FF ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L151-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L151-L156

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

theorem GlobalTheory.LatPair.Model.FF_ne_zero [Fintype n] (q : Unif k) {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1) {φ : Form k n M}
    (h : φ ∈ Mram k n M) (h0 : FF q χ φ = 0) : φ = 0 := by sorry
