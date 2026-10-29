-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_eq_toPMF_realWeightedSum
-- name    : LIDT.MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:04.399714+00:00
-- url     : https://prove2.me/theorems/f64e9303-4ca9-4f3e-b693-e677e994fce2
-- title:
--   Avg Over Eq To PMF Real Weighted Sum
-- statement:
--   **A probabilistic distribution average agrees with its PMF expectation.** Let $\mathcal D$ be a finite weighted distribution on $\alpha$ with total mass one, and let $f:\alpha\to\mathbb R$ be error-valued. Write $P_{\mathcal D}$ for the associated probability mass function and $W(P,f)$ for the real weighted sum of $f$ under a PMF $P$. Then
--
--   $$
--   \operatorname{avgOver}(\mathcal D,f)=W(P_{\mathcal D},f).
--   $$
--
--   This is the bridge between the LIDT weighted-distribution API and the finite PMF API.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionPMF.lean#L63-L69

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
import Mathlib.Probability.ProbabilityMassFunction.Monad

open LIDT
/-!
# PMF expectations associated to project distributions

This module relates the project `Distribution` averaging notation to the finite
expectation `PMF.realWeightedSum` on Mathlib probability mass functions.  The
statements keep the project-facing averages available while allowing later
probability arguments to cite the associated Mathlib `PMF` object directly.
The module-valued finite-sum algebra for uniform project distributions lives in
`MIPStarRE.LDT.Basic.DistributionUniformSums`; this file records the additional
comparison with `PMF.realWeightedSum`.

## Main declarations

* `avgOver_eq_toPMF_realWeightedSum`
* `averageOperatorOverDistribution_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSumLinearMap`
* `uniformDistribution_sum_smul_eq_pmf_realWeightedSum`
* `avgOver_uniform_eq_pmf_realWeightedSum`
* `averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

theorem LIDT.MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum {α : Type*} [Fintype α]
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 f = PMF.realWeightedSum (𝒟.toPMF h𝒟) f := by sorry
