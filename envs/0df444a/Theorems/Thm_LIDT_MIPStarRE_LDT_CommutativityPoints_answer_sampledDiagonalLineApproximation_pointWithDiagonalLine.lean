-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
-- name    : LIDT.MIPStarRE.LDT.CommutativityPoints.answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T14:08:41.655096+00:00
-- url     : https://prove2.me/theorems/b87c3b9f-c89b-448c-b79d-b09b765d2291
-- title:
--   Answer Sampled Diagonal Line Approximation Point With Diagonal Line
-- statement:
--   **Answer-valued point versus diagonal-line approximation.**
--
--   Let $S$ be an answer-valued symmetric strategy with normalized state, field-valued point answers, and function-valued diagonal-line answers. Assume that its axis-parallel, self-consistency, and diagonal-line failure probabilities are at most $\varepsilon$, $\delta$, and $\gamma$. For a uniformly sampled diagonal line $\ell$ and parameter $t\in\mathbb{F}_q$, compare the point measurement at the sampled point $\ell(t)$ with the diagonal-line measurement for $\ell$ postprocessed by the evaluation map $f\mapsto f(t)$. On the two registers, their state-dependent squared distance satisfies
--
--   $$
--   \operatorname{SDDRel}_{\psi,\mathcal U_{\mathrm{DiagLine}\times\mathbb{F}_q}}\!\left(A_{\ell(t)}\otimes I,\ I\otimes L^{\ell}_{[f(t)]};\,2m\gamma\right).
--   $$
--
--   The answer-valued formulation keeps the full function answer until this final postprocessing, so it applies the transport-covariant function-answer interface directly. It supplies the approximation input used by `answerCommutativityPoints`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.CommutativityPoints.answer_sampledDiagonalLineApproximation_pointWithDiagonalLine`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/CommutativityPoints/Approximation.lean#L607-L807

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

open LIDT
/-!
# Section 10 — commutativity points approximation layer

Restricted-diagonal approximation infrastructure for commutativity at points.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

lemma LIDT.MIPStarRE.LDT.CommutativityPoints.answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat params ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
        (fun q =>
          (strategy.pointMeasurement (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointFromDiagonalQuestion params q)).toSubMeas))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma) := by sorry
