-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_switchSandwich_rightTransfer
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich_rightTransfer
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:04.495107+00:00
-- url     : https://prove2.me/theorems/78a99d3d-564a-4275-8fde-76f2987d9b33
-- title:
--   Switch Sandwich Right Transfer
-- statement:
--   **Switch-sandwich transfer from the middle expression to the right expression.**
--
--   Let `psi` be normalized, let `D` be a question distribution whose support weights sum to at most one, let `A` be an indexed projective submeasurement, and let `B` satisfy `OpBounded01`. If `A` is bipartite SDD-consistent with itself at error `delta`, then
--
--   $$
--   \left|\operatorname{middleSandwichExpectation}(\psi,D,A,B)
--   -\operatorname{rightSandwichExpectation}(\psi,D,A,B)\right|
--   \leq \sqrt{\delta}.
--   $$
--
--   Here the middle expectation averages `ev psi (leftTensor B * rightTensor (A_q,a))`. The right expectation averages `ev psi (leftTensor (B * (A_q,a)))`, so the estimate transfers the right-register outcome factor into the left operator product. The proof bounds the pointwise difference by the lifted self-distance and then averages over questions using the distribution weight condition. This closes the second half of the switch-sandwich comparison used by the commutativity and pasting results.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.switchSandwich_rightTransfer`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/RightTransfer.lean#L24-L450

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Switch-sandwich main: middle-to-right transfer

The middle-to-right transfer estimate used in `prop:switch-sandwich`.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich_rightTransfer
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas Question Outcome ι)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op ι) (hB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 B)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas A)
      (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas A) δ →
    |_root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B -
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.rightSandwichExpectation ψ 𝒟 A B| ≤
      Real.sqrt δ := by sorry
