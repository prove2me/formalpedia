-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_glued_injective
-- name    : GlobalTheory.LatPair.Model.glued_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:56.53163+00:00
-- url     : https://prove2.me/theorems/feb0c8e5-2151-5d38-ae32-71c7a2fd0142
-- title:
--   Model: glued injective
-- statement:
--   The Model construction uses the glued injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L186-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L186-L205

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

theorem GlobalTheory.LatPair.Model.glued_injective (q : Unif k) {c p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) :
    Function.Injective fun P : Pair k n => P.glued q c p := by sorry
