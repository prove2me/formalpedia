-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_exists_FF_ne_zero
-- name    : GlobalTheory.LatPair.Model.exists_FF_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:34.488843+00:00
-- url     : https://prove2.me/theorems/2d7dff6c-62bf-43c7-a151-deea27e0cb5b
-- title:
--   Model: exists FF ne zero
-- statement:
--   The Model construction uses the exists FF ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L214-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L214-L220

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

theorem GlobalTheory.LatPair.Model.exists_FF_ne_zero [Fintype n] [Nonempty n] {c : 𝓀[k]ˣ} (hc : c ≠ 1) :
    ∃ (q : Unif k) (ψ : AddChar k Circle) (hψ : SplitWeil.HasConductor ψ 1) (φ : Form k n ℂ),
      φ ∈ Mram k n ℂ ∧ FF q (resChar ψ hψ q) φ ≠ 0 := by sorry
