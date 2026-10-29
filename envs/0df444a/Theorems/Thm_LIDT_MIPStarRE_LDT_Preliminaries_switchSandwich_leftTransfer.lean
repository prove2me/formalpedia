-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_switchSandwich_leftTransfer
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich_leftTransfer
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:30:04.653066+00:00
-- url     : https://prove2.me/theorems/4cd79df8-91c4-44ff-9d0a-14e73ecc6c9e
-- title:
--   Switch Sandwich Left Transfer
-- statement:
--   **Switch-sandwich transfer from the left expression to the middle expression.**
--
--   Let `psi` be a normalized bipartite state, `D` a question distribution whose support weights sum to at most one, `A` an indexed projective submeasurement, and `B` an operator satisfying `OpBounded01`. If the family `A` is bipartite SDD-consistent with itself at error `delta`, then
--
--   $$
--   \left|\operatorname{leftSandwichExpectation}(\psi,D,A,B)
--   -\operatorname{middleSandwichExpectation}(\psi,D,A,B)\right|
--   \leq 2\sqrt{\delta}.
--   $$
--
--   The left expectation averages over questions the sum of expectations of `A_a B A_a` with all three factors placed on the left register. The middle expectation averages the sum with `B` on the left and the outcome operator `A_a` on the right. The proof applies the left and middle question-gap estimates to an intermediate mixed expression, then uses the SDD error bound and the triangle inequality. The result is used by the commutativity and pasting arguments.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.switchSandwich_leftTransfer`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/LeftTransfer.lean#L28-L145

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
# Switch-sandwich main: left-to-middle transfer

The left-to-middle transfer estimate used in `prop:switch-sandwich`, bounding
the gap between the left and middle expressions via the Cauchy–Schwarz-based
gap bounds.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich_leftTransfer
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
    |_root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψ 𝒟 A B -
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B| ≤
      2 * Real.sqrt δ := by sorry
