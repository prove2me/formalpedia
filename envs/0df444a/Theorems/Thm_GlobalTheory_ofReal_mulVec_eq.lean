-- Prove2me | Theorems.Thm_GlobalTheory_ofReal_mulVec_eq
-- name    : GlobalTheory.ofReal_mulVec_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:54.679165+00:00
-- url     : https://prove2.me/theorems/e43c538c-0f69-489b-ab20-92ff9258ef4d
-- title:
--   Global Theory: of Real mul Vec eq
-- statement:
--   The Global Theory construction uses the of Real mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L54-L57

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
omit [DecidableEq ι]

theorem GlobalTheory.ofReal_mulVec_eq (P : Matrix ι ι ℝ) (x : ι → ℝ) :
    (fun i => ((P *ᵥ x) i : ℂ)) = P.map ofReal *ᵥ fun i => (x i : ℂ) := by sorry
