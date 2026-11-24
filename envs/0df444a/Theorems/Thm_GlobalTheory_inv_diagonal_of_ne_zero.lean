-- Prove2me | Theorems.Thm_GlobalTheory_inv_diagonal_of_ne_zero
-- name    : GlobalTheory.inv_diagonal_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:56.509698+00:00
-- url     : https://prove2.me/theorems/0c3a3969-48b4-428b-9482-9160372778b7
-- title:
--   Global Theory: inv diagonal of ne zero
-- statement:
--   The Global Theory construction uses the inv diagonal of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L87-L92

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

theorem GlobalTheory.inv_diagonal_of_ne_zero {t : ι → ℂ} (ht : ∀ i, t i ≠ 0) :
    (diagonal t)⁻¹ = diagonal fun i => (t i)⁻¹ := by sorry
