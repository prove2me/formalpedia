-- Prove2me | Theorems.Thm_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
-- name    : NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/dc8f0f75-8a4c-5854-8069-a53494435857
-- title:
--   Splitting of the S-part idelic measure over ℤ^S
-- statement:
--   Let $F$ be a number field, $S$ a finite set of height-one primes of $\mathcal{O}_F$, and consider the unit group of the adele ring $\mathbb{A}_F = \mathbb{A}_{F,\infty} \times \mathbb{A}_{F,\mathrm{fin}}$ equipped with its Borel $\sigma$-algebra `ideleBorel F`. For a finite set $S$ the measure `sPartMeasure F S` is the push-forward along the monoid homomorphism `partAt F S` induced on units by `partAtAdele F S` of the Haar measure `idelicHaar F` restricted to the subgroup `unitIdelesOutside` of those ideles $\delta$ such that, for every $v \notin S$, both the $v$-component of the finite part of $\delta$ and that of $\delta^{-1}$ lie in $\mathcal{O}_{F_v}$. Write $\operatorname{ord}_v(a) = -\log \lvert a_v \rvert_v$ for the negated $\mathbb{Z}$-valued logarithm of the $v$-adic valuation of the finite component of an idele $a$. The assertion is: for every measurable $f : \mathbb{A}_F^\times \to [0,\infty]$ that factors through the archimedean component (i.e. $f(a) = f(b)$ whenever the first components of $a$ and $b$ in $\mathbb{A}_{F,\infty}$ agree), and every family of weights $\varphi_v : \mathbb{Z} \to [0,\infty]$ indexed by height-one primes,
--   $$\int^- f(a) \prod_{v \in S} \varphi_v(\operatorname{ord}_v a)\, d(\mathrm{sPartMeasure}\ F\ S) = \Big(\int^- f \, d(\mathrm{sPartMeasure}\ F\ \emptyset)\Big) \cdot \prod_{v \in S} \sum_{m \in \mathbb{Z}} \varphi_v(m),$$
--   the inner sum being an unconditional sum in $[0,\infty]$. No measurability or summability hypothesis on the $\varphi_v$ is required.
--
--   This is the restricted-product decomposition of the Haar measure of the idele class group in the form used here: the $S$-part measure factors as its archimedean ($S = \emptyset$) part times counting measure on the order vectors $(\operatorname{ord}_v)_{v \in S} \in \mathbb{Z}^S$. It is the computational engine behind the shell and ball estimates for Rankin–Selberg integrals ([`AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery`](thm.html#AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery), [`AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery)) and behind the factorisation of integrability used in the cubic induction for Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.Idele IsDedekindDomain
open scoped ENNReal

theorem NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable[ideleBorel F] f)
    (hf1 : ∀ a b : (AdeleRing (𝓞 F) F)ˣ, ((a : AdeleRing (𝓞 F) F)).1 = ((b : AdeleRing (𝓞 F) F)).1 → f a = f b)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) :
    (∫⁻ a, f a * ∏ v ∈ S, φ v (ord F v a) ∂(sPartMeasure F S)) =
      (∫⁻ a, f a ∂(sPartMeasure F ∅)) * ∏ v ∈ S, ∑' m : ℤ, φ v m := by sorry
