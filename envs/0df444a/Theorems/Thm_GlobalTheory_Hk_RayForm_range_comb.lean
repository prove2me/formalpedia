-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayForm_range_comb
-- name    : GlobalTheory.Hk.RayForm.range_comb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:34:52.253907+00:00
-- url     : https://prove2.me/theorems/c24a076b-4f7e-40d9-af18-3fda5e63a903
-- title:
--   Ray Form: range comb
-- statement:
--   The Ray Form construction uses the range comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassIdealCountEqNcardShiftedBinaryForm.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassIdealCountEqNcardShiftedBinaryForm.lean#L77-L80

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

theorem GlobalTheory.Hk.RayForm.range_comb (f₁ f₂ : ℂ) :
    Set.range (fun v : ℤ × ℤ => (v.1 : ℂ) * f₁ + v.2 * f₂) = (Submodule.span ℤ {f₁, f₂} : Submodule ℤ ℂ) := by sorry
