-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_riemannTheta_eq_neg_inv
-- name    : GlobalTheory.IsSiegel.riemannTheta_eq_neg_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:37.305194+00:00
-- url     : https://prove2.me/theorems/b15a3f2d-2084-42e1-87c8-46de0ed17132
-- title:
--   Is Siegel: riemann Theta eq neg inv
-- statement:
--   The Is Siegel construction uses the riemann Theta eq neg inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L257-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L257-L311

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

theorem GlobalTheory.IsSiegel.riemannTheta_eq_neg_inv {σ : Matrix ι ι ℂ} (h : IsSiegel σ) (a : ι → ℝ)
    (w : ι → ℂ) :
    riemannTheta a 0 σ w = siegelGaussIntegral σ * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) *
      riemannTheta 0 a (-σ⁻¹) (σ⁻¹ *ᵥ w) := by sorry
