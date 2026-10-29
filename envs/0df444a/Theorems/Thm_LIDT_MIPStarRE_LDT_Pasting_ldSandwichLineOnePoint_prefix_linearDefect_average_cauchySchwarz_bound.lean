-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound
-- name    : LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T16:44:25.937824+00:00
-- url     : https://prove2.me/theorems/e3d3c847-465a-4574-9511-720f7fc508f4
-- title:
--   Ld Sandwich Line One Point Prefix Linear Defect Average Cauchy Schwarz Bound
-- statement:
--   **The averaged linear consistency defect obeys the same two-root transport bound.**
--
--   Let $(m,q,d)$ have a field model, let $S$ be a symmetric successor strategy, let $G^x$ be an indexed slice polynomial family, and let $\gamma,\zeta$ be errors. Fix $i<k$ with $i\ne0$ and assume the adjoint raw-core bound. With $P^{\mathrm{orig}}_q$, $P^{\mathrm{mov}}_q$, and $R^i_q$ as in the preceding result, define $\Lambda_{\psi}$ by the total-minus-matching formula. Then
--
--   $$
--   \mathbb E_q\Lambda_{\psi}(P^{\mathrm{orig}}_q,R^i_q)
--   \le
--   \mathbb E_q\Lambda_{\psi}(P^{\mathrm{mov}}_q,R^i_q)+2\sqrt{\nu_{i+1}},
--   $$
--
--   where the averages are uniform over $\mathcal Q_k$ and
--
--   $$
--   \nu_{i+1}=426(i+1)^2m\left(\operatorname{rpow}(\gamma,1/16)+\operatorname{rpow}(\zeta,1/16)+\operatorname{rpow}(d/q,1/16)\right).
--   $$
--
--   The option-valued original and moved families have zero $\bot$ effect, while the right family is complete. The option expansion therefore identifies both linear defects with the scalar sums in the preceding theorem, allowing the scalar inequality to be transferred directly.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CauchySchwarz.lean#L567-L650

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Section 12 pasting: line one-point transport — Cauchy-Schwarz chain

Internal helper module; part of the file-split for `#1127`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : _root_.LIDT.MIPStarRE.LDT.Pasting.LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)) (fun q =>
      _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect strategy.state
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixOriginalFamily params family hi) q)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q))
      ≤
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)) (fun q =>
      _root_.LIDT.MIPStarRE.LDT.Pasting.qBipartiteLinearConsDefect strategy.state
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixMovedFamily params family hi) q)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i) q)) +
      2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta (i + 1)) := by sorry
