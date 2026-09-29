-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
-- name    : LanglandsTunnell.CubicInduction.integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/6989c23a-4f6d-5356-97d2-0b92621c7d1f
-- title:
--   Middle identity for a double torus Whittaker integral
-- statement:
--   Let $K$ be a field carrying a locally compact topological ring structure, let $K^\times$ be equipped with a measurable structure for which multiplication is measurable, and let $\mu$ be a left-invariant measure on $K^\times$. Let $\psi$ be an additive character of $K$ with values in $\mathbb{C}$ and let $W \colon \mathrm{GL}_3(K) \to \mathbb{C}$ satisfy the Whittaker transformation law `IsGL3PsiWhittakerFn`: $W(n(x,y,z)g) = \psi(x+y)W(g)$ for all $x,y,z \in K$ and all $g$, where $n(x,y,z)$ is the upper unipotent matrix with entries $(1,2) = x$, $(2,3) = y$, $(1,3) = z$. Let $\omega \colon K^\times \to \mathbb{C}^\times$ be a homomorphism such that $W(\mathrm{diag}(z,z,z)\,g) = \omega(z)W(g)$ for all $z \in K^\times$ and all $g$, let $\chi_0, \chi_1 \colon K^\times \to \mathbb{C}^\times$ be homomorphisms, let $s \in \mathbb{C}$ and let $u \in K^\times$. Write $c(a,t) = \chi_1(a)^{-1}\omega(a)^{-1}|a|^{s}\cdot\chi_0(t)|t|^{-s-1}$, where $|\cdot| =$ `modulus` is the module of $K$ (the factor by which multiplication scales additive Haar measure, extended by $0$ at $0$), write $d(t,a) = \mathrm{diag}(ta, a, 1) \in \mathrm{GL}_3(K)$ for the image under `iotaGL` of $\mathrm{diag}(ta,a) \in \mathrm{GL}_2(K)$, let $w_3$ be the antidiagonal permutation matrix `longWeyl3`, $w' =$ `weylPrime3` the permutation matrix exchanging the last two coordinates, and $n_{13}(c) = n(0,0,c)$. Then
--   $$\int_{K^\times}\!\int_{K^\times} c(a,t)\,W\big(d(t,a)\,w_3\,n_{13}(u)\,w'\big)\,d\mu(t)\,d\mu(a) = \chi_0(-1)\chi_0(u)\chi_1(u)^{-1}|u|^{-1}\int_{K^\times}\!\int_{K^\times} c(a,t)\,W\big(d(t,a)\,w_3\,n_{13}(u^{-1})\,w_3\,w'\big)\,d\mu(t)\,d\mu(a),$$
--   the integrals being Bochner integrals over $\mu$, in the inner variable $t$ and the outer variable $a$. No integrability hypothesis is imposed.
--
--   This is the middle step in the local computation establishing multiplicativity of the $\mathrm{GL}_3 \times \mathrm{GL}_2$ Rankin–Selberg $\gamma$-factor in the $\mathrm{GL}_2$ variable for a principal-series partner $I(\chi_0,\chi_1)$: it matches the representative on the big Bruhat cell used on the primal side with the one used on the dual side, up to the displayed character and modulus factors. It is used by the two results producing the primal and dual middle data for $\iota$-invariant dominant sections, and by the identity relating the double torus integral to an integral over the unipotent radical of $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
    {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    [MeasurableSpace Kˣ] [MeasurableMul Kˣ] (μ : Measure Kˣ) [μ.IsMulLeftInvariant]
    (ψ : AddChar K ℂ) (W : GL (Fin 3) K → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : Kˣ →* ℂˣ)
    (hω : ∀ (z : Kˣ) (g : GL (Fin 3) K), W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (χ₀ χ₁ : Kˣ →* ℂˣ) (s : ℂ) (u : Kˣ) :
    (∫ a : Kˣ, ∫ t : Kˣ,
        (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
          (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) *
        W (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 (u : K) * weylPrime3)) ∂μ ∂μ) =
      ((χ₀ (-1) : ℂˣ) : ℂ) * ((χ₀ u : ℂˣ) : ℂ) * ((χ₁ u : ℂˣ) : ℂ)⁻¹ * (((modulus (u : K) : ℝ) : ℂ))⁻¹ *
      ∫ a : Kˣ, ∫ t : Kˣ,
        (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
          (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) *
        W (iotaGL (diagUnits2 (t * a) a) *
          (longWeyl3 * upperUnipotent3 0 0 ((u⁻¹ : Kˣ) : K) * longWeyl3 * weylPrime3)) ∂μ ∂μ := by sorry
