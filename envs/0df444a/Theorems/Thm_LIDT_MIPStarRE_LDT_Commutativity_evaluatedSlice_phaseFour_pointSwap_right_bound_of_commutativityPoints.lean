-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
-- name    : LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:01.402302+00:00
-- url     : https://prove2.me/theorems/248fac02-dd2a-4ee2-8779-c020fc7e466a
-- title:
--   Evaluated Slice Phase Four Point Swap Right Bound Of Commutativity Points
-- statement:
--   **Commutativity points control the evaluated-slice right-register swap.** Fix a parameter record with a field model, a normalized symmetric strategy on the successor dimension, and an error `gamma`. Assume the strategy's point-measurement products satisfy `SDDOpRel` under the uniform point-pair distribution with defect `commutativityPointsError` for the given parameters and `gamma`. For every evaluated-slice question $q$ and outcome pair $ab$, let $C(q,ab)$ be an operator whose squared sum is at most the identity. Compare the averaged expectation obtained by placing the point measurement for $q.2$ before $q.1$ with the one obtained in the ordered order.
--
--   Let $\mathcal D$ be the uniform distribution on the evaluated-slice questions for the given parameter record. Then
--
--   $$
--   \left|\operatorname{avgOver}(\mathcal D,\mathrm{inserted})
--   -\operatorname{avgOver}(\mathcal D,\mathrm{swapped})\right|
--   \le 6\sqrt{\gamma\,(m+1)}.
--   $$
--
--   The estimate is the phase-four point-swap bound derived directly from the commutativity-points relation; the subsequent `evaluatedSlice_phaseFour_pointSwap_right_bound` supplies the same conclusion from `strategy.IsGood`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/PointSwap.lean#L27-L154

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Point-swap bound for the evaluated-slice paper chain

This file contains the right-register point-swap estimate used in the
paper-faithful scalar chain for `lem:comm-data-processed-g`.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (hcomm :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma))
    (C : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params →
      _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι))
    (hC : ∀ q, ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1) :
    let 𝒟 := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
    let inserted : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (C q ab *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
               ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))
    let swapped : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (C q ab *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
               ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swapped| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by sorry
