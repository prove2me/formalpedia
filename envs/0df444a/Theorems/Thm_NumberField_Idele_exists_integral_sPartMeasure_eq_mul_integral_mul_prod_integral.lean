-- Prove2me | Theorems.Thm_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral
-- name    : NumberField.Idele.exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/fabe651a-d213-5a56-a71e-3db9d088e5c5
-- title:
--   Splitting of integrals for the S-part of idelic Haar measure
-- statement:
--   Let $F$ be a number field and $S$ a finite set of height-one primes of $\mathcal{O}_F$ (finite places). The unit group $(\mathbb{A}_F)^\times$ of the adele ring is equipped with the Borel $\sigma$-algebra of its topology. Assume given a measurable, Borel structure on $(\mathbb{A}_{F,\infty})^\times$ together with a Haar measure $\nu_A$ on it, and, for every finite place $w$, a measurable, Borel structure on $(F_w)^\times$ (the units of the adic completion) together with a measure $\mu_w$, required to be Haar for $w \in S$. Then there exists a real $c > 0$, depending only on these data, with the following property. Let $f$ be a complex function on $(\mathbb{A}_F)^\times$, $g$ one on $(\mathbb{A}_{F,\infty})^\times$, and $h_w$ one on each $(F_w)^\times$. Suppose that for every idele $a$ whose finite component at each $w \notin S$ equals $1$ one has $f(a) = g(\mathrm{infPart}\,a)\prod_{w\in S} h_w(\mathrm{finPart}_w\,a)$, where `infPart` is induced on unit groups by the projection to the infinite adeles and $\mathrm{finPart}_w$ by projection to the finite adeles followed by evaluation at $w$; suppose also that $f$ is almost everywhere strongly measurable for the measure `sPartMeasure F S`, the push-forward under the unit-group endomorphism induced by `partAtAdele F S` of the idelic Haar measure `idelicHaar F` restricted to the subgroup of ideles whose finite part $\delta$ satisfies $\delta_v, (\delta^{-1})_v \in \mathcal{O}_v$ for all $v \notin S$. Then $\int f \, d(\mathrm{sPartMeasure}\,F\,S) = c \cdot \bigl(\int g \, d\nu_A\bigr) \cdot \prod_{w \in S} \int h_w \, d\mu_w$.
--
--   This is the measure-theoretic factorisation underlying Tate's local–global decomposition of idelic integrals: the Haar measure of the idele group, restricted to the ideles that are local units outside $S$ and pushed to the part at $S$ and at infinity, is a positive multiple of the product of Haar measures on $(\mathbb{A}_{F,\infty})^\times$ and the $(F_w)^\times$ for $w \in S$, so that integrals of functions factorising along these coordinates split into a product of local integrals. It is used in the cubic induction step of the Langlands–Tunnell input, where an idelic integral is written as an archimedean factor times a local factor at a chosen place times a factor supported at the remaining places of $S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel in

theorem NumberField.Idele.exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (νA : Measure (InfiniteAdeleRing F)ˣ) [νA.IsHaarMeasure]
    [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)ˣ]
    [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)ˣ]
    (μ : ∀ w : HeightOneSpectrum (𝓞 F), Measure (w.adicCompletion F)ˣ)
    (hμ : ∀ w ∈ S, (μ w).IsHaarMeasure) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (g : (InfiniteAdeleRing F)ˣ → ℂ)
        (h : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ → ℂ),
        (∀ a : (AdeleRing (𝓞 F) F)ˣ,
          (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) →
            f a = g (M4aHerbrand.infPart a) * ∏ w ∈ S, h w (M4aHerbrand.finPart w a)) →
        AEStronglyMeasurable f (NumberField.Idele.sPartMeasure F S) →
          ∫ a, f a ∂(NumberField.Idele.sPartMeasure F S) =
            c * (∫ u, g u ∂νA) * ∏ w ∈ S, ∫ t, h w t ∂(μ w) := by sorry
