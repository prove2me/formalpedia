-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_le_avgOver_add_totalVariationDistance
-- name    : LIDT.MIPStarRE.LDT.avgOver_le_avgOver_add_totalVariationDistance
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:09.339833+00:00
-- url     : https://prove2.me/theorems/954ab057-7fa3-4e9c-8311-05d832bc6bed
-- title:
--   Avg Over Le Avg Over Add Total Variation Distance
-- statement:
--   **Bounded expectations change by at most total variation.** Let `μ` and `ν` be probability distributions and let `f : α → Error` take values in `[0,1]`. Then replacing `μ` by `ν` can increase the average by no more than the total variation distance between the two distributions.
--
--   $$
--   \bigl(\forall a,\ 0 \le f(a) \le 1\bigr)
--   \;\Longrightarrow\;
--   \operatorname{avgOver}\,ν\,f
--   \le \operatorname{avgOver}\,μ\,f
--     + \operatorname{totalVariationDistance}(μ,ν).
--   $$
--
--   This is the distribution-replacement estimate used in the pasting bounds comparing distinct-tuple sampling with uniform sampling.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.avgOver_le_avgOver_add_totalVariationDistance`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionAvg.lean#L331-L401

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

theorem LIDT.MIPStarRE.LDT.avgOver_le_avgOver_add_totalVariationDistance {α : Type*} [DecidableEq α]
    (μ ν : _root_.LIDT.MIPStarRE.LDT.Distribution α) (hμ : μ.IsProbability) (hν : ν.IsProbability)
    (f : α → _root_.LIDT.MIPStarRE.LDT.Error)
    (hf_nonneg : ∀ a, 0 ≤ f a)
    (hf_le_one : ∀ a, f a ≤ 1) :
    _root_.LIDT.MIPStarRE.LDT.avgOver ν f ≤ _root_.LIDT.MIPStarRE.LDT.avgOver μ f + _root_.LIDT.MIPStarRE.LDT.totalVariationDistance μ ν := by sorry
