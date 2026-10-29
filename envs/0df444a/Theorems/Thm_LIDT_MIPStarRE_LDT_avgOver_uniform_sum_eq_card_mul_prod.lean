-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_uniform_sum_eq_card_mul_prod
-- name    : LIDT.MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:40:38.62916+00:00
-- url     : https://prove2.me/theorems/124cc2cf-1677-4c61-a2a4-f67a58f0907d
-- title:
--   Avg Over Uniform Sum Eq Card Mul Prod
-- statement:
--   **A finite sum inside a uniform average becomes a product average.** For finite nonempty types `α` and `β` and a scalar family `f : α → β → Error`, averaging the sum over `β` is the cardinality of `β` times the uniform average over the product `α × β`.
--
--   $$
--   \operatorname{avgOver}(\operatorname{uniformDistribution}\,α)\,(\lambda a\,\Rightarrow \sum_{b : β} f(a,b))
--   = (\operatorname{Fintype.card}\,β)\,\operatorname{avgOver}(\operatorname{uniformDistribution}(α \times β))\,(\lambda ab\,\Rightarrow f(ab.1,ab.2)).
--   $$
--
--   This is the normalization and reindexing identity used when the commutativity proof exchanges a uniform question average with a finite outcome sum.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionAvg.lean#L659-L690

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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

theorem LIDT.MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => ∑ b : β, f a b) =
      (Fintype.card β : _root_.LIDT.MIPStarRE.LDT.Error) *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by sorry
