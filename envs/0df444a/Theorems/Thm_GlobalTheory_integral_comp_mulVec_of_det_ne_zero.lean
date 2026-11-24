-- Prove2me | Theorems.Thm_GlobalTheory_integral_comp_mulVec_of_det_ne_zero
-- name    : GlobalTheory.integral_comp_mulVec_of_det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:56.414714+00:00
-- url     : https://prove2.me/theorems/6c23b5b4-66e1-43f0-8b1f-972fd8bcc8ee
-- title:
--   Global Theory: integral comp mul Vec of det ne zero
-- statement:
--   The Global Theory construction uses the integral comp mul Vec of det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L120-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L120-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.integral_comp_mulVec_of_det_ne_zero {P : Matrix ι ι ℝ} (hP : P.det ≠ 0)
    {f : (ι → ℝ) → ℂ} (hf : Continuous f) :
    ∫ x, f (P *ᵥ x) = (|P.det⁻¹| : ℝ) * ∫ y, f y := by sorry
