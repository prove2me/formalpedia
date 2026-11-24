-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayForm_exists_equiv
-- name    : GlobalTheory.Hk.RayForm.exists_equiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:34:40.447605+00:00
-- url     : https://prove2.me/theorems/ec2016fe-5391-4599-9849-81970cf98299
-- title:
--   Ray Form: exists equiv
-- statement:
--   The Ray Form construction uses the exists equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassIdealCountEqNcardShiftedBinaryForm.lean#L82-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassIdealCountEqNcardShiftedBinaryForm.lean#L82-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayForm
open GlobalTheory.Mem.PartialZeta

theorem GlobalTheory.Hk.RayForm.exists_equiv (f₁ f₂ e₁ e₂ : ℂ) (hf : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0)
    (he : ((starRingEnd ℂ) e₁ * e₂).im ≠ 0)
    (h : Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂}) :
    ∃ σ : ℤ × ℤ ≃ ℤ × ℤ, ∀ v, (v.1 : ℂ) * f₁ + v.2 * f₂ = (σ v).1 * e₁ + (σ v).2 * e₂ := by sorry
