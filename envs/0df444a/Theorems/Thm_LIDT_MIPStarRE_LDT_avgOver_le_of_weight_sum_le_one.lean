-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_le_of_weight_sum_le_one
-- name    : LIDT.MIPStarRE.LDT.avgOver_le_of_weight_sum_le_one
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:40:28.996241+00:00
-- url     : https://prove2.me/theorems/57bd0488-ca6e-4415-a218-fc61a5792ec6
-- title:
--   Avg Over Le Of Weight Sum Le One
-- statement:
--   **A sub-probability average obeys a nonnegative pointwise upper bound.** Let $\mathcal D$ be a distribution on $\alpha$, let $f:\alpha\to\mathbb R$ be an error-valued family, and let $\delta\ge0$. Write $w(a)$ for the stored weight and $M=\sum_{a\in\operatorname{supp}(\mathcal D)}w(a)$. If $M\le1$ and $f(a)\le\delta$ for every $a$, then
--
--   $$
--   M\le1,\quad \delta\ge0,\quad (\forall a\in\alpha)\;f(a)\le\delta
--   \quad\Longrightarrow\quad \operatorname{avgOver}(\mathcal D,f)\le\delta.
--   $$
--
--   This is the scalar averaging estimate used when an incomplete distribution is bounded by a uniform error budget.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.avgOver_le_of_weight_sum_le_one`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionAvg.lean#L165-L178

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

theorem LIDT.MIPStarRE.LDT.avgOver_le_of_weight_sum_le_one {α : Type*} (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α)
    (f : α → _root_.LIDT.MIPStarRE.LDT.Error) (δ : _root_.LIDT.MIPStarRE.LDT.Error)
    (h𝒟 : ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1)
    (hδ_nonneg : 0 ≤ δ)
    (hf : ∀ a, f a ≤ δ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 f ≤ δ := by sorry
