-- Prove2me | Theorems.Thm_GlobalTheory_Hk_rayCountTheta_fibre_tsum
-- name    : GlobalTheory.Hk.rayCountTheta_fibre_tsum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:29.475795+00:00
-- url     : https://prove2.me/theorems/5a23e1c2-3713-4cce-97f8-27a852f562b0
-- title:
--   Hk: ray Count Theta fibre tsum
-- statement:
--   The Hk construction uses the ray Count Theta fibre tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayCountThetaFibreCount.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayCountThetaFibreCount.lean#L35-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayCountThetaFibreCount
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
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.rayCountTheta_fibre_tsum {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq : ∀ v, Q v = q v) (t : ℝ)
    (hs : Summable fun v => Real.exp (-(t * Q v))) :
    ∑' n : ℕ, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n)) = ∑' v, Real.exp (-(t * Q v)) := by sorry
