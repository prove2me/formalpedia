-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_exists_FF_ne_zero_three
-- name    : GlobalTheory.LatPair.Model.exists_FF_ne_zero_three
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:11.527068+00:00
-- url     : https://prove2.me/theorems/78ca9a9b-feff-46be-bf28-f6c76f06face
-- title:
--   Model: exists FF ne zero three
-- statement:
--   The Model construction uses the exists FF ne zero three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L224-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L224-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_SplitWeil_Model_padic_localField

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

theorem GlobalTheory.LatPair.Model.exists_FF_ne_zero_three :
    letI := SplitWeil.Model.padic_localField 3
    ∃ (q : Unif ℚ_[3]) (ψ : AddChar ℚ_[3] Circle) (hψ : SplitWeil.HasConductor ψ 1) (φ : Form ℚ_[3] (Fin 2) ℂ),
      φ ∈ Mram ℚ_[3] (Fin 2) ℂ ∧ FF q (resChar ψ hψ q) φ ≠ 0 := by sorry
