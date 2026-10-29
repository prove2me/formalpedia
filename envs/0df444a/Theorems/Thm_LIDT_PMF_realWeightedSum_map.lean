-- Prove2me | Theorems.Thm_LIDT_PMF_realWeightedSum_map
-- name    : LIDT.PMF.realWeightedSum_map
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:03.364247+00:00
-- url     : https://prove2.me/theorems/953ce569-24dc-413f-b67b-81491d1296a2
-- title:
--   Real Weighted Sum Map
-- statement:
--   **Push-forward formula for a finite PMF-weighted sum.** Let $p$ be a probability mass function on $\alpha$, let $e:\alpha\to\beta$, and let $f:\beta\to M$, where $M$ is an additive commutative monoid and an $\mathbb R$-module. Write $p_e$ for the push-forward of $p$ along $e$, and write $W(P,g)$ for the real weighted sum of $g$ under a PMF $P$. Then
--
--   $$
--   W(p_e,f)=W\bigl(p,\,a\mapsto f(e(a))\bigr).
--   $$
--
--   This is the finite expectation change-of-variables rule for mapped PMFs.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `PMF.realWeightedSum_map`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/PMFAverages.lean#L490-L498

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Monad

open LIDT
/-!
# PMF-weighted finite expectation identities

This module contains finite expectation identities stated directly for
Mathlib probability mass functions.  They connect `PMF.map` and
`PMF.bind` to the real-weighted finite sums used by the
low individual degree test averaging layer.

## Main declarations

* `PMF.map_apply_toReal`
* `PMF.realWeightedSum`
* `PMF.realWeightedSumLinearMap`
* `PMF.realWeightedSum_map`
* `PMF.realWeightedSum_bind`
* `PMF.map_sum_smul`
* `PMF.bind_apply_toReal`
* `PMF.bind_sum_smul`
* `PMF.sum_toReal_eq_one`
* `PMF.sum_const_smul`
* `PMF.totalVariationDistance`
* `PMF.totalVariationDistance_eq_sum_max_sub`
* `PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq`
* `PMF.sum_le_sum_add_totalVariationDistance`
* `PMF.sum_rpow_one_div_le_rpow_sum`
* `PMF.realWeightedSum_rpow_one_div_le_rpow`
* `PMF.uniformOfFintype_map_equiv`
* `PMF.uniformOfFintype_prod_apply_toReal`
* `PMF.uniformOfFintype_prod_eq_bind`
* `PMF.uniformOfFintype_sum_equiv_smul`
* `PMF.uniformOfFintype_prod_sum_smul`
* `PMF.uniformOfFintype_sum_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_equiv_snd_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_snd_smul`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators



open LIDT.PMF

theorem LIDT.PMF.realWeightedSum_map {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module _root_.LIDT.MIPStarRE.LDT.Error M]
    (p : PMF α) (e : α → β) (f : β → M) :
    _root_.LIDT.PMF.realWeightedSum (p.map e) f = _root_.LIDT.PMF.realWeightedSum p (fun a => f (e a)) := by sorry
