-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_exists_integral_cexp_quadratic
-- name    : GlobalTheory.IsSiegel.exists_integral_cexp_quadratic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:35.000444+00:00
-- url     : https://prove2.me/theorems/fb1a76ac-82db-4351-9432-2bab66a2ea8a
-- title:
--   Is Siegel: exists integral cexp quadratic
-- statement:
--   The Is Siegel construction uses the exists integral cexp quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L130-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L130-L173

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

theorem GlobalTheory.IsSiegel.exists_integral_cexp_quadratic {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    ∃ s : ℂ, s ^ 2 * (-I • σ).det = 1 ∧ ∀ w : ι → ℂ,
      ∫ x : ι → ℝ, cexp (2 * π * I * (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 +
        (fun i => (x i : ℂ)) ⬝ᵥ w)) = s * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) := by sorry
