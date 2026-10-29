-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_totalVariationDistance_eq_sum_max_sub
-- name    : LIDT.MIPStarRE.LDT.totalVariationDistance_eq_sum_max_sub
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:40:28.858903+00:00
-- url     : https://prove2.me/theorems/c815724c-d288-49a9-bf48-6825bcbd0cde
-- title:
--   Total Variation Distance Eq Sum Max Sub
-- statement:
--   **Total variation is the positive part of the signed mass difference.** Let $\mu$ and $\nu$ be probability distributions on $\alpha$. Write $S=\operatorname{supp}(\mu)\cup\operatorname{supp}(\nu)$, and write $w_\mu(a)$ and $w_\nu(a)$ for their stored weights. Then
--
--   $$
--   \operatorname{TV}(\mu,\nu)=\sum_{a\in S}\max\{0,w_\nu(a)-w_\mu(a)\}.
--   $$
--
--   Here $\operatorname{TV}$ denotes the total variation distance used by the development. Equal total mass makes this positive-excess form equal to the usual half-$L^1$ distance.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.totalVariationDistance_eq_sum_max_sub`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionAvg.lean#L261-L329

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

theorem LIDT.MIPStarRE.LDT.totalVariationDistance_eq_sum_max_sub {α : Type*} [DecidableEq α]
    (μ ν : _root_.LIDT.MIPStarRE.LDT.Distribution α) (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    _root_.LIDT.MIPStarRE.LDT.totalVariationDistance μ ν =
      ∑ a ∈ μ.support ∪ ν.support, max 0 (ν.weight a - μ.weight a) := by sorry
