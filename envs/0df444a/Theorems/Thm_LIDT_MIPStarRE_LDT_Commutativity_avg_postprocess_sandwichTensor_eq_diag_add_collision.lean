-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_avg_postprocess_sandwichTensor_eq_diag_add_collision
-- name    : LIDT.MIPStarRE.LDT.Commutativity.avg_postprocess_sandwichTensor_eq_diag_add_collision
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:59:58.238639+00:00
-- url     : https://prove2.me/theorems/b07b0f38-28ac-4da9-8071-e259a241ad57
-- title:
--   Avg Postprocess Sandwich Tensor Eq Diag Add Collision
-- statement:
--   **A postprocessed tensor sandwich splits into its diagonal term and collision residual.**
--
--   Let $\psi$ be a bipartite quantum state, let $A$ and $B$ be submeasurements with finite outcome sets $\alpha$ and $\beta$, let $\sigma$ be a finite nonempty sampling type, and let $\mathrm{eval}:\sigma\to\alpha\to\kappa$ be a finite-outcome postprocessing map. For each sample $s$, expand the sandwich built from $B_b$ and the postprocessed effect $A_{[\mathrm{eval}(s)=k]}$. The uniform average over $s$, $k$, and $b$ equals the diagonal contribution plus the off-diagonal contribution weighted by the probability that two original outcomes collide under `eval`:
--
--   $$
--   \begin{aligned}
--   \mathbb{E}_{s}\sum_{k,b}\operatorname{ev}_\psi\!\left[(B_bA_{[\mathrm{eval}(s)=k]}B_b)\otimes A_{[\mathrm{eval}(s)=k]}\right]
--   ={}&\sum_{a,b}\operatorname{ev}_\psi\!\left[(B_bA_aB_b)\otimes A_a\right]\\
--   &+\sum_{a,a',b}\mathbf{1}_{a\ne a'}\Pr_s[\mathrm{eval}(s,a)=\mathrm{eval}(s,a')]\operatorname{ev}_\psi\!\left[(B_bA_aB_b)\otimes A_{a'}\right].
--   \end{aligned}
--   $$
--
--   This exact expansion is the algebraic basis for the full-slice marginalization arguments in both coordinate directions.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Commutativity.avg_postprocess_sandwichTensor_eq_diag_add_collision`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean#L393-L495

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
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

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Full-slice tensor marginalization core

Collision residuals, postprocessing expansions, and tensor marginalization
core bounds for the `BABA` and `ABAB` full-slice tensor averages.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma LIDT.MIPStarRE.LDT.Commutativity.avg_postprocess_sandwichTensor_eq_diag_add_collision
    {α β σ κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype κ] [DecidableEq κ]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (A : _root_.LIDT.MIPStarRE.LDT.SubMeas α ι) (B : _root_.LIDT.MIPStarRE.LDT.SubMeas β ι) (eval : σ → α → κ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (B.outcome b * (_root_.LIDT.MIPStarRE.LDT.postprocess A (eval s)).outcome k * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.postprocess A (eval s)).outcome k))) =
      (∑ a : α, ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)) *
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome aa.2)) := by sorry
