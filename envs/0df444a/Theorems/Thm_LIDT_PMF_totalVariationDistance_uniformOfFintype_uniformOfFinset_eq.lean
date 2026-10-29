-- Prove2me | Theorems.Thm_LIDT_PMF_totalVariationDistance_uniformOfFintype_uniformOfFinset_eq
-- name    : LIDT.PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:34.793749+00:00
-- url     : https://prove2.me/theorems/d71333d0-efc8-42e5-a8c0-dc626a40ba6b
-- title:
--   Total Variation Distance Uniform Of Fintype Uniform Of Finset Eq
-- statement:
--   **Total variation between ambient and subset-uniform distributions.**
--
--   Let $\alpha$ be a finite nonempty type and let $s\subseteq\alpha$ be a nonempty finite subset. Compare the uniform PMF on all of $\alpha$ with the PMF that is uniform on $s$. Their total variation distance is determined only by the relative size of the subset:
--
--   $$
--   \operatorname{TV}\bigl(\operatorname{Unif}(\alpha),\operatorname{Unif}(s)\bigr)
--   =
--   1-\frac{|s|}{|\alpha|}.
--   $$
--
--   The cardinalities in the displayed expression are interpreted in the real error field. This calculation quantifies the loss caused by conditioning uniform sampling on a nonempty finite subset and is used in the LIDT pasting estimates.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/PMFAverages.lean#L642-L703

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

theorem LIDT.PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq
    {α : Type*} [Fintype α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    _root_.LIDT.PMF.totalVariationDistance (PMF.uniformOfFintype α) (PMF.uniformOfFinset s hs) =
      1 - (s.card : _root_.LIDT.MIPStarRE.LDT.Error) / (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error) := by sorry
