-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSlice_scalar_chain_bound
-- name    : LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_scalar_chain_bound
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:19.476322+00:00
-- url     : https://prove2.me/theorems/df26e005-11e0-448b-a3d1-7f7a4c74c172
-- title:
--   Evaluated Slice Scalar Chain Bound
-- statement:
--   **The evaluated-slice scalar chain gives the processed commutativity error.**
--
--   Let `params` and `strategy` be as above, let $\gamma$ and $\zeta$ be errors, and let `family` and `G` satisfy the conversion hypothesis `hG`. Assume `hnorm`, `hcomm`, `hgamma_nonneg`, `hcons`, `hself`, `hbound`, and `hpostSSC`, with the corresponding point and slice errors. The ten scalar moves compare the averaged $\mathsf{ABA}$ and $\mathsf{ABAB}$ terms and yield
--
--   $$
--   2\left(\mathbb{E}_{q}\left[\mathsf{ABA}(q)\right]-\mathbb{E}_{q}\left[\mathsf{ABAB}(q)\right]\right)\le48m\left(\gamma^{1/2}+\zeta^{1/2}\right).
--   $$
--
--   The right side is `commDataProcessedGError params gamma zeta`; the insertion, point-swap, stability, reverse-insertion, and postprocessed self-consistency moves are assembled in this bound.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Commutativity.evaluatedSlice_scalar_chain_bound`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/MainChain.lean#L166-L802

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
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
# Main scalar chain assembly

The core lemma `evaluatedSlice_scalar_chain_bound` that assembles the ten-step
scalar approximation chain for `lem:comm-data-processed-g`.  This is the
heavyweight proof corresponding to `references/ldt-paper/commutativity-G.tex`,
lines 72–131.  Phases 1, 3, 4, 6–7, and 8–9 are supplied by the reverse and
tail parts of the paper chain; Phase 2 uses the reindexing infrastructure from
`PhaseTwo`.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











/- Scalar approximation chain for the evaluated-slice commutation.

This is the core of the paper's proof of `lem:comm-data-processed-g`
(`references/ldt-paper/commutativity-G.tex`, lines 72–131).
Starting from `E[∑ ABAB]`, the proof applies ten approximation steps:

1. `≈_{2√ζ}`: insert Bob's measurement via `closenessOfIP` + `eq:add-an-a`
2. `≈_{√ζ}`: remove trailing `G^y` (`clm:g-comm-stability`)
3. `≈_{2√ζ}`: insert Bob's second measurement via `closenessOfIP` +
   `eq:add-an-a`
4. `≈_{6√(γ(m+1))}`: swap Bob's measurements via `closenessOfIP` +
   `commutativityPoints`
5a. `≈_{6√(γ(m+1))}`: the point-measurement swap contribution internal
    to the paper's `clm:g-comm-stability2` accounting
5b. `≈_{√ζ}`: remove trailing `G^x` by the boundedness part of
    `gCommStabilityTwo_raw_scalar` (this is the scalar part of `hphase5paper` below)
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. -/

lemma LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_scalar_chain_bound
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (_hnorm : strategy.state.IsNormalized)
    (_hcomm :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma))
    (_hgamma_nonneg : 0 ≤ gamma)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (_hG : ∀ x, G x = (family.meas x).toSubMeas)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (_hpostSSC : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family)
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family)
      zeta) :
    2 *
      (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab)) ≤
      _root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta := by sorry
