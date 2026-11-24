-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_add_map_ofReal
-- name    : GlobalTheory.IsSiegel.add_map_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:50.051288+00:00
-- url     : https://prove2.me/theorems/c6c81566-990b-4107-a45c-bb58d1f61626
-- title:
--   Is Siegel: add map of Real
-- statement:
--   The Is Siegel construction uses the add map of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L110-L115

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
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.IsSiegel.add_map_ofReal {σ : Matrix ι ι ℂ} (h : IsSiegel σ) {C : Matrix ι ι ℝ}
    (hC : C.IsSymm) : IsSiegel (σ + C.map ofReal) := by sorry
