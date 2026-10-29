-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_sum_ev_mul_leftBounded_le_of_leftHermitian
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.sum_ev_mul_leftBounded_le_of_leftHermitian
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:08.623494+00:00
-- url     : https://prove2.me/theorems/3fbccbb3-4965-454a-b19f-f6c57e76a056
-- title:
--   Sum Ev Mul Left Bounded Le Of Left Hermitian
-- statement:
--   **A Hermitian contraction gives a summed expectation Cauchy-Schwarz bound.**
--
--   For a quantum state `psi`, an operator `LB`, and finite outcome-indexed operator families `X` and `Y`, assume that `LB` is Hermitian and satisfies `LB * LB <= 1`. Also assume every `X a` and `Y a` is Hermitian. Then
--
--   $$
--   \left|\sum_a \operatorname{ev}_{\psi}\bigl(X_a(LB Y_a)\bigr)\right|
--   \leq
--   \sqrt{\sum_a \operatorname{ev}_{\psi}(X_aX_a)}\,
--   \sqrt{\sum_a \operatorname{ev}_{\psi}(Y_a^{\dagger}Y_a)}.
--   $$
--
--   The contraction hypothesis controls the second factor after inserting `LB`, while Hermiticity supplies the adjoint simplifications and nonnegative quadratic expectations. This is the shared analytic estimate used to prove both question-level switch-sandwich gap bounds.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.sum_ev_mul_leftBounded_le_of_leftHermitian`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Core.lean#L25-L76

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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Switch-sandwich gap bounds: Cauchy–Schwarz core

Shared Cauchy–Schwarz contraction used in both the left and middle gap
estimates of the switch-sandwich argument.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma LIDT.MIPStarRE.LDT.Preliminaries.sum_ev_mul_leftBounded_le_of_leftHermitian
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι)
    (LB : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (X Y : Outcome → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hLB_herm : LBᴴ = LB)
    (hLB_sq_le_one : LB * LB ≤ 1)
    (hXherm : ∀ a, (X a)ᴴ = X a)
    (hYherm : ∀ a, (Y a)ᴴ = Y a) :
    |∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (X a * (LB * Y a))| ≤
      Real.sqrt (∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (X a * X a)) *
        Real.sqrt (∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((Y a)ᴴ * Y a)) := by sorry
