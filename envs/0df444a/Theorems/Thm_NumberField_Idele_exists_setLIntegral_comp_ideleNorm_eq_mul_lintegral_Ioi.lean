-- Prove2me | Theorems.Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
-- name    : NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/6b9cb5c3-c41d-5794-8a34-2812044bfad0
-- title:
--   Norm disintegration of idelic Haar measure on a fundamental domain
-- statement:
--   Let $K$ be a number field, and give the idele group $(\mathbb{A}_K)^\times = (\text{AdeleRing } \mathcal{O}_K\,K)^\times$ its Borel $\sigma$-algebra (`ideleBorel`, with the corresponding `BorelSpace` instance), and let `idelicHaar K` be the Haar measure `Measure.haar` on it. Let $D$ be a subset of the idele group, assumed measurable, and assumed to be a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain` for `idelicHaar K`, for the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) of principal ideles, that is the range of the map on unit groups induced by the structure morphism $K \to \mathbb{A}_K$. Write $\|z\| =$ `ideleNorm K z` for the real number obtained from the value at $z$ of the distributive Haar character `distribHaarChar` of the additive group $\mathbb{A}_K$, i.e. the module of $z$. The assertion is that there exists $V \in [0,\infty]$ with $V \neq 0$ and $V \neq \infty$ such that for every measurable $f : \mathbb{R} \to [0,\infty]$, the lower Lebesgue integral of $z \mapsto f(\|z\|)$ over $D$ against `idelicHaar K` equals $V \cdot \int_{(0,\infty)} f(y)\,y^{-1}\,dy$, the latter taken against Lebesgue measure on $\mathbb{R}$ restricted to $(0,\infty)$, with $y^{-1}$ read in $[0,\infty]$ via `ENNReal.ofReal`. The constant $V$ does not depend on $f$.
--
--   This is the unfolding of Haar measure on the idele class group along the idele norm, in the form used in Tate's treatment of global zeta functions: integration over a fundamental domain for $K^\times$ of a function of the norm alone reduces to integration against $dy/y$ on $(0,\infty)$, with $V$ the covolume of $K^\times$ in the norm-one ideles. It is invoked in the integral computations for pseudo-Eisenstein series and the associated Maass–Selberg type identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi.lean

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

theorem NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hD : MeasurableSet D)
    (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K)) :
    ∃ V : ℝ≥0∞, V ≠ 0 ∧ V ≠ ∞ ∧ ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹ := by sorry
