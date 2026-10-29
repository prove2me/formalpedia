-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_question_switchSandwich_left_gap
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_left_gap
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:26:23.922271+00:00
-- url     : https://prove2.me/theorems/7736c4de-e07d-4d2a-9517-41effb3ebdc9
-- title:
--   Question Switch Sandwich Left Gap
-- statement:
--   **Question switch-sandwich left gap.**
--
--   Let `psi` be a normalized bipartite quantum state, let `A` be a projective submeasurement on a finite index type, and let `B` be an operator satisfying `OpBounded01`. The absolute difference between the two outcome sums
--
--   $$
--   \sum_a \operatorname{ev}_{\psi}(A_a \otimes I\; B \otimes I\; A_a \otimes I)
--   $$
--
--   and
--
--   $$
--   \sum_a \operatorname{ev}_{\psi}(A_a \otimes I\; B \otimes A_a)
--   $$
--
--   is at most the square root of `qSDD psi A.liftLeft A.liftRight`. In the formal statement, the tensor placements are expressed by `leftTensor` and `rightTensor`, and the submeasurement lifts are taken from `A.toSubMeas`.
--
--   This is the first pointwise gap estimate in the switch-sandwich transfer. It measures the cost of replacing the final left copy of an outcome operator by its right copy while retaining the left copy of `A` and the bounded middle operator `B`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.question_switchSandwich_left_gap`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Left.lean#L31-L258

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Switch-sandwich gap bounds: left gap

The left gap estimate `question_switchSandwich_left_gap`, bounding the
question-level left gap of the switch-sandwich argument.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

-- NOTE: `question_switchSandwich_left_gap` and `question_switchSandwich_middle_gap`
-- are each ~330 lines. The shared OpBounded01 setup has been extracted into
-- `leftTensor_opBounded01_*` helpers above. The shared
-- `sum_ev_mul_leftBounded_le_of_leftHermitian` lemma now packages the
-- Cauchy-Schwarz application plus the `LB * LB ≤ 1` sandwich contraction,
-- while the two long proofs keep their distinct rewrite skeletons.

lemma LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_left_gap
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas Outcome ι)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op ι) (hB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 B) :
    |(∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))| ≤
      Real.sqrt
        (_root_.LIDT.MIPStarRE.LDT.qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by sorry
