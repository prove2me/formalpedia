-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_question_switchSandwich_middle_gap
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_middle_gap
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:26:31.10953+00:00
-- url     : https://prove2.me/theorems/40671fe0-9300-48c0-a276-eb6d6747c471
-- title:
--   Question Switch Sandwich Middle Gap
-- statement:
--   **Question switch-sandwich middle gap.**
--
--   Let `psi` be normalized, let `A` be a projective submeasurement, and let `B` satisfy `OpBounded01`. The absolute difference between
--
--   $$
--   \sum_a \operatorname{ev}_{\psi}(A_a \otimes I\; B \otimes A_a)
--   $$
--
--   and
--
--   $$
--   \sum_a \operatorname{ev}_{\psi}(B \otimes A_a)
--   $$
--
--   is bounded by `sqrt (qSDD psi A.toSubMeas.liftLeft A.toSubMeas.liftRight)`. The formal expression uses `leftTensor` for the first copy, `rightTensor` for the second copy, and the same operator `B` in the left register.
--
--   This is the second pointwise gap estimate in the switch-sandwich chain. It removes the remaining left outcome factor and leaves the middle sandwich expression, with the same self-distance quantity controlling the replacement.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.question_switchSandwich_middle_gap`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Middle.lean#L25-L302

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
# Switch-sandwich gap bounds: middle gap

The middle gap estimate `question_switchSandwich_middle_gap`, bounding the
question-level middle gap of the switch-sandwich argument.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_middle_gap
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas Outcome ι)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op ι) (hB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 B) :
    |(∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))| ≤
      Real.sqrt
        (_root_.LIDT.MIPStarRE.LDT.qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by sorry
