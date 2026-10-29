-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_averageOperatorOverDistribution_mul_left_right
-- name    : LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_mul_left_right
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:40:28.885795+00:00
-- url     : https://prove2.me/theorems/78b317f9-c159-4754-9877-3c94e5d1760d
-- title:
--   Average Operator Over Distribution Mul Left Right
-- statement:
--   **Fixed left and right operator factors pass through an average.** For an operator family `A` over a finite-support distribution `𝒟`, multiplying every value on the left by `L` and on the right by `R` is the same as multiplying the averaged operator by those fixed factors.
--
--   $$
--   \operatorname{averageOperatorOverDistribution}\,𝒟\,(\lambda a\,\Rightarrow L\,A(a)\,R)
--   = L\,\operatorname{averageOperatorOverDistribution}\,𝒟\,A\,R.
--   $$
--
--   The theorem provides the linearity step used by commutativity marginalization arguments and by averaged sandwich bounds in pasting.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.averageOperatorOverDistribution_mul_left_right`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionAvg.lean#L180-L191

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open LIDT
/-!
# Average lemmas for finite-support distributions

This module contains the finite-sum and uniform-average lemmas for the project
`Distribution` type.  The primitive distribution definitions, uniform
distributions, and total variation distance live in
`MIPStarRE.LDT.Basic.Distribution`.

## Main declarations

The main results are the algebraic rules for `avgOver`, scalar and
operator-valued forms of the module-valued finite-sum rules for uniform
distributions, and the comparison between finite uniform averages and Mathlib
uniform probability mass functions.

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

/-! ### Averaging infrastructure

Linearity proofs use `Distribution.weightedSumLinearMap`; order and support
estimates use Mathlib's `Finset.sum` API. -/

theorem LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_mul_left_right {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (L R : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (A : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution 𝒟 (fun a => L * A a * R) =
      L * _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution 𝒟 A * R := by sorry
