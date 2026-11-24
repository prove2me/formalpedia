-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_FF_eq_D_Gs
-- name    : GlobalTheory.LatPair.Model.FF_eq_D_Gs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:04.492344+00:00
-- url     : https://prove2.me/theorems/f812f3a3-cd20-4120-96d0-8d60b970d898
-- title:
--   Model: FF eq D Gs
-- statement:
--   The Model construction uses the FF eq D Gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L118-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L118-L149

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

theorem GlobalTheory.LatPair.Model.FF_eq_D_Gs (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FF q χ φ = D q (Gs χ φ) := by sorry
