-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sampledDiagonalLineApproximation_pointWithDiagonalLine
-- name    : LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_pointWithDiagonalLine
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T14:08:39.898679+00:00
-- url     : https://prove2.me/theorems/0f570c7d-336d-48c0-b837-ed0450d13870
-- title:
--   Sampled Diagonal Line Approximation Point With Diagonal Line
-- statement:
--   **Point measurement versus sampled diagonal-line evaluation.**
--
--   Let $S$ be a symmetric strategy with parameters $(q,m,d)$ and normalized state, and assume its three test failure probabilities are bounded by $\varepsilon$, $\delta$, and $\gamma$. Sample a diagonal line $\ell$ uniformly and then a parameter $t\in\mathbb{F}_q$ on that line. The point measurement is taken at the sampled point $\ell(t)$; the comparison measurement is the diagonal-line measurement for $\ell$, postprocessed by evaluating its polynomial answer at $t$. After placing the two measurements on the left and right registers, their state-dependent squared distance under the uniform line-and-parameter distribution is bounded by
--
--   $$
--   \operatorname{SDDRel}_{\psi,\mathcal U_{\mathrm{DiagLine}\times\mathbb{F}_q}}\!\left(A_{\ell(t)}\otimes I,\ I\otimes L^{\ell}_{[f(t)]};\,2m\gamma\right).
--   $$
--
--   Here $L^{\ell}_{[f(t)]}$ is the diagonal-line answer measurement after evaluation at $t$. This transports the restricted diagonal-line approximation estimate to the point-with-diagonal-line distribution and is used by the two subsequent ignore-coordinate lemmas.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_pointWithDiagonalLine`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/CommutativityPoints/Approximation.lean#L333-L480

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

lemma LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_pointWithDiagonalLine
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledPointMeasurement params strategy))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma) := by sorry
