-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_answerCommutativityPoints
-- name    : LIDT.MIPStarRE.LDT.CommutativityPoints.answerCommutativityPoints
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:18:52.577711+00:00
-- url     : https://prove2.me/theorems/ed0117eb-77e0-4380-8edb-a2868f17e451
-- title:
--   Answer Commutativity Points
-- statement:
--   **Commutativity of answer-valued point products.**
--
--   Let $S$ be an answer-valued symmetric strategy for the low individual degree test with parameters $(q,m,d)$, normalized bipartite state $\psi$, point measurements with field-valued answers, and diagonal-line measurements with function-valued answers. Suppose its axis-parallel, self-consistency, and diagonal-line test failure probabilities are bounded by $\varepsilon$, $\delta$, and $\gamma$, respectively. For a uniformly sampled pair of points $(u,v)\in(\mathbb{F}_q^m)^2$, let $P_L(u,v)$ have outcome $(a,b)$ equal to $(A^u_aA^v_b)\otimes I$, and let $P_R(u,v)$ have outcome $(a,b)$ equal to $(A^v_bA^u_a)\otimes I$. Then
--
--   $$
--   \operatorname{SDDOpRel}_{\psi,\mathcal U_{(\mathbb{F}_q^m)^2}}\!\left(P_L,P_R;\,32m\gamma\right).
--   $$
--
--   The relation means that the uniform average of the state-dependent squared operator distance between the ordered and reversed products is at most $32m\gamma$. This answer-valued theorem is the point-commutativity input used by `answerComMainForCarrier_ofAnswerGood`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.CommutativityPoints.answerCommutativityPoints`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean#L854-L957

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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
# Section 10 commutativity points: answer-valued diagonal measurements
This file proves the commutativity-at-points theorem using the answer-valued
diagonal-line verifier relation.  The conclusion concerns only the point
measurements, hence it can later be transferred to the ordinary carrier used by
self-improvement, but the proof does not use the carrier's inert diagonal
measurement.
## References
- `references/ldt-paper/commutativity-points.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

theorem LIDT.MIPStarRE.LDT.CommutativityPoints.answerCommutativityPoints
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat params ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.answerPointMeasurementProductLeft params strategy)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.answerPointMeasurementProductRight params strategy)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params gamma) := by sorry
