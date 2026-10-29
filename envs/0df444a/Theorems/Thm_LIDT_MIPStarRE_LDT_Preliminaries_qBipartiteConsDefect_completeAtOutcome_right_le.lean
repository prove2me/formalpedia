-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_qBipartiteConsDefect_completeAtOutcome_right_le
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:35.679998+00:00
-- url     : https://prove2.me/theorems/8dbba49c-0687-4844-9405-603ba57d6b54
-- title:
--   Q Bipartite Cons Defect Complete At Outcome Right Le
-- statement:
--   **Completing the right submeasurement increases bipartite defect by at most the missing mass.**
--
--   Let `A` be a left measurement, `B` a right submeasurement, and `a0` the completion outcome. For any bipartite state, the consistency defect after completing `B` is bounded by its original defect plus the expectation of the right residual effect:
--
--   $$
--   \operatorname{qBipartiteConsDefect}(\psi,A,\operatorname{completeAtOutcome}(B,a_0))
--   \le\operatorname{qBipartiteConsDefect}(\psi,A,B)
--   +\operatorname{ev}_{\psi}\left(\operatorname{rightTensor}(1-B.\operatorname{total})\right).
--   $$
--
--   The bound isolates exactly the mass added on the right. It is used when converting submeasurement consistency estimates into completed measurement estimates.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Completion.lean#L155-L247

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
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
# Preliminary comparison theorems: bipartite self-consistency (completion)

Completion-transfer lemmas for bipartite self-consistency.  The constant
`Unit`-family reductions identify `sddError` and `sscError` with their pointwise
forms, and the later lemmas compare a submeasurement with its completion.

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma LIDT.MIPStarRE.LDT.Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
    {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιA)
    (B : _root_.LIDT.MIPStarRE.LDT.SubMeas Outcome ιB)
    (a0 : Outcome) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas ≤
      _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B +
        _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) (1 - B.total)) := by sorry
