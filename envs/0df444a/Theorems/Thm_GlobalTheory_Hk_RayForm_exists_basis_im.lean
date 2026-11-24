-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayForm_exists_basis_im
-- name    : GlobalTheory.Hk.RayForm.exists_basis_im
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:35:10.386791+00:00
-- url     : https://prove2.me/theorems/c8bf52ac-edde-4595-bad3-e83d35b83f9d
-- title:
--   Ray Form: exists basis im
-- statement:
--   The Ray Form construction uses the exists basis im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassIdealCountEqNcardShiftedBinaryForm.lean#L133-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassIdealCountEqNcardShiftedBinaryForm.lean#L133-L181

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
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Hk.RayForm.exists_basis_im {d : ℕ} (hp : d.Prime) (hd : d % 4 = 3) {x : K} (hx : x ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) :
    ∃ b : Module.Basis (Fin 2) ℤ (𝓞 K),
      (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ^ 2 = d / 4 := by sorry
