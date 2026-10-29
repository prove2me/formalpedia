-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_uniform_equiv_prod
-- name    : LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_prod
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:04.53601+00:00
-- url     : https://prove2.me/theorems/3ea0718d-a1d4-420e-af77-c1fd82daa0d3
-- title:
--   Avg Over Uniform Equiv Prod
-- statement:
--   **Uniform averaging transported through a product equivalence.**
--
--   Let $\gamma$, $\alpha$, and $\beta$ be finite nonempty types, let $e:\gamma\simeq\alpha\times\beta$ be an equivalence, and let $f:\gamma\to\mathbb{R}$ be an error-valued function. The uniform average of $f$ over $\gamma$ can be computed by transporting each pair $(a,b)$ back along $e$ and taking iterated uniform averages:
--
--   $$
--   \mathbb{E}_{x\sim\mathrm{Unif}(\gamma)} f(x)
--   =
--   \mathbb{E}_{a\sim\mathrm{Unif}(\alpha)}\,\mathbb{E}_{b\sim\mathrm{Unif}(\beta)} f\bigl(e^{-1}(a,b)\bigr).
--   $$
--
--   This is the finite change-of-variables identity that converts a uniform average over an encoded domain into separate averages over product coordinates. It supports the repeated reindexing and factorization of averages used throughout the LIDT development.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.avgOver_uniform_equiv_prod`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionAvg.lean#L692-L704

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

theorem LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_prod
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : γ ≃ α × β) (f : γ → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution γ) f =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α)
        (fun a => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β) (fun b => f (e.symm (a, b)))) := by sorry
