-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_consRel_constPolynomialEvaluation_heterogeneous
-- name    : LIDT.MIPStarRE.LDT.Test.consRel_constPolynomialEvaluation_heterogeneous
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:26:32.063745+00:00
-- url     : https://prove2.me/theorems/eec1000b-a147-44dc-be2d-88f136d049c8
-- title:
--   Cons Rel Const Polynomial Evaluation Heterogeneous
-- statement:
--   **Constant-family polynomial consistency lifts to pointwise evaluation consistency.**
--
--   Let `A` and `B` be polynomial-valued measurements on possibly different registers. If their constant submeasurement families are consistent under the uniform distribution on `Unit` with error `delta`, then evaluating the polynomials at a uniformly sampled point preserves the same heterogeneous consistency error:
--
--   $$
--   \operatorname{ConsRel}(\operatorname{const}(A),\operatorname{const}(B),\delta)
--   \Longrightarrow
--   \operatorname{ConsRel}(\operatorname{polynomialEvaluationFamily}(A),
--   \operatorname{polynomialEvaluationFamily}(B),\delta).
--   $$
--
--   The theorem transports the constant test to the point-question test without changing the error. It is used in the projective evaluation consistency argument and in the source role-register final-point theorem.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.consRel_constPolynomialEvaluation_heterogeneous`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ProjectiveConsistency/Evaluation.lean#L85-L144

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.LDT.Test
end LIDT.MIPStarRE.LDT.Test

open LIDT
/-!
# Projective consistency evaluation

This module contains the data-processing lemmas which turn polynomial-level
projective consistency into pointwise consistency after evaluation at a sampled
point.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem LIDT.MIPStarRE.LDT.Test.consRel_constPolynomialEvaluation_heterogeneous
    {params : _root_.LIDT.MIPStarRE.LDT.Parameters} [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA) (B : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB)
    {δ : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B.toSubMeas) δ) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params B.toSubMeas) δ := by sorry
