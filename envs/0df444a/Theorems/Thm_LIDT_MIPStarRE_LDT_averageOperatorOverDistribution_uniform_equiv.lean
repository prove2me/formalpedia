-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_averageOperatorOverDistribution_uniform_equiv
-- name    : LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_uniform_equiv
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:40:24.865203+00:00
-- url     : https://prove2.me/theorems/389d5c54-5ee6-41c9-938e-719bd355adcf
-- title:
--   Average Operator Over Distribution Uniform Equiv
-- statement:
--   **Uniform operator averages are invariant under finite reindexing.**
--
--   Let $\alpha$ and $\beta$ be finite nonempty types, let $\iota$ be a finite index type with decidable equality, let $e:\alpha\simeq\beta$ be an equivalence, and let $f:\alpha\to\operatorname{Op}(\iota)$ be an operator family. Averaging $f$ uniformly over $\alpha$ equals averaging the transported family $b\mapsto f(e^{-1}(b))$ uniformly over $\beta$:
--
--   $$
--   \operatorname{averageOperatorOverDistribution}(\operatorname{Unif}(\alpha),f)
--   =
--   \operatorname{averageOperatorOverDistribution}\bigl(\operatorname{Unif}(\beta),\,b\mapsto f(e^{-1}(b))\bigr).
--   $$
--
--   The identity permits finite question spaces to be replaced by equivalent product or subtype presentations in the LIDT averaging arguments.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.averageOperatorOverDistribution_uniform_equiv`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionAvg.lean#L487-L498

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

theorem LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_uniform_equiv
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (f : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f =
      _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)
        (fun b => f (e.symm b)) := by sorry
