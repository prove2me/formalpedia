-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_conjBlock_of_re_gt
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_conjBlock_of_re_gt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/4bf66380-3e5b-5fff-9baf-3c03004e06c9
-- title:
--   Dual torus pair equals Γ_ℝ times conjugate-block torus triple
-- statement:
--   Fix a real archimedean parameter $P_2$ (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$, of central exponent $u_1+u_2$, or $\mathrm{discrete}(u,k)$, of central exponent $2u$), write $c_2=P_2.\mathrm{centralExponent}$, and let $D$ be an archimedean Whittaker datum for $P_2$ (a function $D.W$ on real $2\times 2$ matrices with the unipotent law $D.W(u(x)g)=e^{2\pi i x}D.W(g)$, the central law, smoothness and the zeta/functional-equation data). Further data: $W:\mathbb R\to\mathbb C$, $a\in\mathbb R$, $u_0,c_P\in\mathbb C$, $a_0,s_P\in\mathbb Z/2$, $k\in\mathbb Z$, $n\in\mathbb N$ and $s\in\mathbb C$. Put $\tilde w=2s-c_P-c_2+n$ and assume $-1<\operatorname{Re}\tilde w$; assume also two integrability hypotheses, namely that for each $a_1\neq 0$ and $a_2>0$ the inner three-variable Iwasawa integrand below is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$, and that the associated four-variable integrand in $(a_2,t,q,p)$, with $|q|$-exponent $u_0+n$, is integrable on $(0,\infty)\times\mathbb R\times\mathbb R\times(0,\infty)$. Then the iterated integral $\int_{a_2>0}\int_{a_1\in\mathbb R}$ of the integrand that vanishes unless $a_1\neq0$ and $a_2>0$, and otherwise equals
--   $$|a_1a_2|\,i^{k}\,|a_1^{-1}|^{c_P+1}\bigl(\mathrm{sgn}(-a_1^{-1})\bigr)^{s_P}\,W(-a_1/a_2)\cdot \chi_{u_0+1,a_0}\!\bigl(-(a_1a_2)^{-1}\bigr)\cdot 2\pi I(a_1,a_2)\cdot|a_1a_2|^{s-1/2}\cdot a_1^{-2},$$
--   where $\chi_{u,\epsilon}(y)=|y|^{u}$ times $\mathrm{sgn}(y)$ if $\epsilon\neq0$ and $1$ if $\epsilon=0$, and $I(a_1,a_2)=\int_{y_1}\int_{y_2>0}\int_x$ of the product of $\exp\bigl(-\pi(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2)\bigr)$, $a_1^2|y_1y_2|$, the section factor $y_1^{-n}\bigl(-aa_1y_2-a_2^{-1}y_2^{-1}+ia_2^{-1}x/y_1\bigr)$, $\exp(-\pi a^2a_1^2y_2^2)$, $\chi_{u_0+2,a_0}((y_1y_2)^{-1})\,|(y_1y_2)^{-1}|^{-2}$, $e^{2\pi i a x}$, $\chi_{c_2,P_2.\mathrm{centralSign}}(y_2)|y_2|$, $D.W\bigl(\mathrm{diag}(ay_1/y_2,1)\bigr)$ and $y_2^2|y_1y_2|^{-4}$, is equal to
--   $$2\pi\, i^{k}\cdot\tfrac12\Gamma_{\mathbb R}(\tilde w+1)\int_{t\in\mathbb R}\int_{q\in\mathbb R}\int_{p>0}\Sigma_n(t,q)\,W(-t)\bigl(-(a+tp^2+ap\,\mathrm{sgn}(t)q^{-1})\bigr)D.W\bigl(\mathrm{diag}(a|t|p/q,1)\bigr)\,|t|^{s-5/2-c_P-c_2}|q|^{u_0+c_P+c_2-2s-1}p^{u_0-c_2-3}e^{-\pi t^2p^2-\pi a^2/p^2-\pi a^2/q^2},$$
--   with $\Sigma_n(t,q)=\chi_{0,s_P}(-t)\chi_{0,a_0}(-t)\chi_{0,1}(t)\chi_{0,n\bmod 2}(q)\chi_{0,a_0}(q)$ a product of signs. Thus the radial variable $a_2$ has been integrated out, converting the $|q|$-exponent $u_0+n$ into $u_0+n-\tilde w-1$ and producing the factor $\tfrac12\Gamma_{\mathbb R}(\tilde w+1)$.
--
--   This is the archimedean radial (Mellin–Gaussian) integration step for the conjugate-block flat section of weight $n+1$: after the Iwasawa unfolding of the dual torus pair the $a_2$-integral is evaluated as a $\Gamma_{\mathbb R}$-factor, leaving a three-variable torus integral in $(t,q,p)$. It is obtained from the pointwise fibre identity [`LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_conjBlock`](thm.html#LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_conjBlock) together with the general Fubini–Gamma lemma [`LanglandsTunnell.Converse.setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre`](thm.html#LanglandsTunnell.Converse.setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre), and it feeds the two weight-one archimedean root-number computations in `LanglandsTunnell.RankinSelberg`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_conjBlock_of_re_gt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_conjBlock_of_re_gt
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (n : ℕ) (s : ℂ)
    (hw : -1 < (2 * s - cP - P₂.centralExponent + n).re)
    (hIW : ∀ a₁ : ℝ, a₁ ≠ 0 → ∀ a₂ : ℝ, 0 < a₂ → Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-((a : ℂ) * (a₁ : ℂ) * (q.2.2 : ℂ)) - (a₂⁻¹ : ℂ) * ((q.2.2⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((q.1 / q.2.1 : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))))
    (hK4 : Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-r.2.1) * ArchR.quasiChar 0 a₀ (-r.2.1) * ArchR.quasiChar 0 1 r.2.1 * ArchR.quasiChar 0 (n : ZMod 2) r.2.2.1 * ArchR.quasiChar 0 a₀ r.2.2.1) *
          (W (-r.2.1) * (-((a : ℂ) + (r.2.1 : ℂ) * (r.2.2.2 : ℂ) ^ 2 + (a : ℂ) * (r.2.2.2 : ℂ) * ArchR.quasiChar 0 1 r.2.1 * ((r.2.2.1⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
          ((((|r.2.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|r.2.2.1| : ℝ) : ℂ) ^ (u₀ + n)) *
            (((r.2.2.2 : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * r.2.1 ^ 2 * r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / r.2.2.1 ^ 2)) : ℂ)))) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))))) :
    (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                ((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (k : ℤ) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) *
                      W (-a₁ / a₂))) *
                  (ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) *
                    (((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
          ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) ^ n * (-((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ)) - (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
      = (((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * ((1 / 2 : ℂ) * Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1))) *
        ∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * (-((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 + (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) := by sorry
