-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
-- name    : LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:59:57.162804+00:00
-- url     : https://prove2.me/theorems/933bfb58-0277-4953-9094-91aa346df477
-- title:
--   Evaluated Slice Phase Two Avg Diff Eq Neg Question Defect
-- statement:
--   **The averaged phase-two subtraction is the negative question defect.**
--
--   Let $(q,m,d)$ have a field model, let $S$ be a symmetric strategy on the successor space, let `family` be a slice-indexed polynomial submeasurement family, and let $G:\mathbb{F}_q\to\operatorname{SubMeas}(\mathcal{P}(m,q,d),\iota)$ agree pointwise with the submeasurements underlying `family`. For a uniformly sampled evaluated-slice question $Q$, define the inserted phase-two quantity by summing over $b$ and $a$ the expectation of the left product $F_1(Q,a)F_2(Q,b)F_1(Q,a)$ against the outcome-$b$ total-sandwich operator at the second point. Define the removed quantity by replacing that total-sandwich operator with the right placement of the second point measurement effect. Then
--
--   $$
--   \mathbb{E}_Q[\mathrm{inserted}(Q)]-\mathbb{E}_Q[\mathrm{removed}(Q)]
--   =-\mathbb{E}_Q[\mathrm{evaluatedSlicePhaseTwoQuestionDefect}(Q)].
--   $$
--
--   This is the uniform-average form of the pointwise phase-two algebra and is the first subtraction identity consumed by `evaluatedSlice_scalar_chain_bound`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/PhaseTwo.lean#L430-L563

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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
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
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Phase 2 stability defect infrastructure

Internal helper definitions and lemmas for the Phase 2 scalar bridge in
`ProcessedG`.  These definitions extract and bound the one-dimensional stability
defect controlled by `gCommStability_scalar` (the paper's `clm:g-comm-stability`),
reindex the question-level defect into the stability defect via finite
marginalization, and perform the subtraction algebra that rewrites the phase-2
insertion/removal difference as the negative defect.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
    let inserted : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)) *
            ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.2).outcome b))
    let removed : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b))
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 removed =
      -_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by sorry
