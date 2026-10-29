-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
-- name    : LIDT.MIPStarRE.LDT.Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:30:13.158796+00:00
-- url     : https://prove2.me/theorems/07853f01-d161-4757-8335-d275343d3fa6
-- title:
--   Projective Evaluation Consistency Of Full Polynomial Consistency Heterogeneous
-- statement:
--   **A projective polynomial SDD relation yields evaluation consistency with halved error.**
--
--   Let `Q_A` and `Q_B` be projective polynomial measurements on two registers. If their constant, left/right placed families satisfy `SDDRel` with error `zeta3` under the unit distribution, then the evaluated polynomial families are consistent under uniform point sampling with error `zeta3 / 2`:
--
--   $$
--   \operatorname{SDDRel}(\operatorname{const}(Q_A),\operatorname{const}(Q_B),\zeta_3)
--   \Longrightarrow
--   \operatorname{ConsRel}(\operatorname{eval}(Q_A),\operatorname{eval}(Q_B),\zeta_3/2).
--   $$
--
--   Projectivity enables the heterogeneous approximation-to-consistency bridge, while the constant-family evaluation lemma moves the result to point questions.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ProjectiveConsistency/Evaluation.lean#L180-L217

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

theorem LIDT.MIPStarRE.LDT.Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
    {params : _root_.LIDT.MIPStarRE.LDT.Parameters} [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    {ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)}
    (Q_A : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA) (Q_B : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB)
    {ζ₃ : _root_.LIDT.MIPStarRE.LDT.Error}
    (hline : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)) ζ₃) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Q_A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Q_B.toSubMeas) (ζ₃ / 2) := by sorry
