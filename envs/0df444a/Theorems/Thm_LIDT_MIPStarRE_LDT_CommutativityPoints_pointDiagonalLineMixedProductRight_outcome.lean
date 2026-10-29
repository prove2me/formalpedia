-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_pointDiagonalLineMixedProductRight_outcome
-- name    : LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight_outcome
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T14:11:47.302747+00:00
-- url     : https://prove2.me/theorems/9eb342bf-f8bf-46da-92ac-108091d71caa
-- title:
--   Point Diagonal Line Mixed Product Right Outcome
-- statement:
--   **Outcome formula for the right mixed point and diagonal-line product.**
--
--   Let $S$ be a symmetric strategy, let $q=(\ell,(t_1,t_2))$ be a shared point-pair diagonal-line question, and let $a,b\in\mathbb{F}_q$. The right mixed family uses the point measurement at the second line point for outcome $b$ and the diagonal-line evaluation at the first line point for outcome $a$. Its outcome operator is
--
--   $$
--   \bigl(M_{\mathrm{mixed,right}}(q)\bigr)_{(a,b)}
--   =A^{\ell(t_2)}_{b}\otimes L^{\ell}_{[f(t_1)=a]}.
--   $$
--
--   The formula identifies the two tensor factors and their outcome coordinates. It is used when the mixed family is compared with the ordered diagonal-line product.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight_outcome`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean#L243-L271

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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints

open LIDT
/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop comparisons.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

lemma LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight_outcome
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params ι)
    (q : _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointPairDiagonalLineQuestion params)
    (a b : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight params strategy) q).outcome (a, b)) =
      _root_.LIDT.MIPStarRE.LDT.opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by sorry
