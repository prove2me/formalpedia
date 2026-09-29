-- Prove2me | Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
-- name    : NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/21f9237c-c705-56eb-8ce9-e42813655e14
-- title:
--   Norm slabs in a fundamental domain have r-independent idelic volume
-- statement:
--   Let $K$ be a number field, and equip the idele group $(\mathbb{A}_K)^\times = (\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$ with the Borel $\sigma$-algebra `ideleBorel` (the Borel structure of its topology) and with the measure `idelicHaar` $=$ `Measure.haar`. Let $D$ be a measurable subset of $(\mathbb{A}_K)^\times$ which is a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain` for `idelicHaar`, for the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) $=$ the image of $K^\times$ under the map of unit groups induced by $K \to \mathbb{A}_K$. Let $e_1, e_2$ be reals with $0 < e_1 < e_2$. Here `ideleNorm K z` denotes the real number obtained from the value at $z$ of the distributive Haar character `distribHaarChar` of the additive group $\mathbb{A}_K$. The assertion is that there exists $C \in [0,\infty]$ with $C \neq 0$ and $C \neq \infty$ such that for every real $r > 0$ the `idelicHaar`-measure of $D \cap \{z : \lVert z\rVert^2 r \in [e_1,e_2]\}$ equals $C$; in particular this measure is positive, finite, and independent of $r$. Despite the name, the conclusion is stated as an equality of measures of sets rather than as a set integral of an indicator function.
--
--   This is the statement that, on a fundamental domain for $K^\times$ in the ideles, a slab cut out by the condition $\lVert z\rVert^2 r \in [e_1,e_2]$ has positive finite volume not depending on the dilation parameter $r$ — the measure-theoretic form of the decomposition of the idele class group as the norm-one class group times $\mathbb{R}_{>0}$, with $d^\times z$ the product of the norm-one measure and $d\rho/\rho$. It supplies the constant by which the central variable integrates out in the Iwasawa disintegration of Rankin–Selberg and twisted Bruhat integrals, and is cited in that context for analyticity and non-vanishing statements about zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ^ 2 * r ∈ Set.Icc e₁ e₂}) = C := by sorry
