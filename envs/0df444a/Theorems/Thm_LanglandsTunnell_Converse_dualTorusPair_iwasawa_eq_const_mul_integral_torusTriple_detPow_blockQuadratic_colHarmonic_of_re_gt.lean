-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_blockQuadratic_colHarmonic_of_re_gt
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_blockQuadratic_colHarmonic_of_re_gt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/2b91bd49-01b1-562e-810a-674ee1e7c042
-- title:
--   Dual torus-pair identity for the block-quadratic section
-- statement:
--   Fix a real archimedean parameter $P_2$ (so $c_2:=P_2.\text{centralExponent}$ is $u_1+u_2$ in the principal case and $2u$ in the discrete case), an archimedean Whittaker datum $D$ for $P_2$ with function $D.W$ on real $2\times 2$ matrices, a function $W:\mathbb R\to\mathbb C$, a real number $a$, complex numbers $u_0,c_P$, signs $a_0,s_P\in\mathbb Z/2$, an integer $k$, a natural number $n$, and $\delta$ with $\delta=0$ or $\delta=1$. Put $\tilde w=2s-c_P-c_2+n$ and assume $\operatorname{Re}\tilde w>-1$. Two integrability hypotheses are assumed: for all $a_1\neq 0$ and $a_2>0$ the inner Iwasawa integrand below is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$, and the four-variable function $(a_2,t,q,p)\mapsto a_2^{\tilde w}e^{-\pi a_2^2q^2}$ times the torus kernel described next, but with $|q|^{u_0+n}$ in place of its power of $|q|$, is integrable on $(0,\infty)\times\mathbb R\times\mathbb R\times(0,\infty)$. The conclusion is an identity of integrals. On the left, $\int_{a_2>0}\int_{a_1\in\mathbb R}$ of the function which, when $a_1\neq 0$ and $a_2>0$, equals $|a_1a_2|\cdot i^k\,|a_1^{-1}|^{c_P+1}\bigl((-a_1^{-1})/|a_1^{-1}|\bigr)^{s_P}\,W(-a_1/a_2)$ times $|a_1a_2|^{-(u_0+1)}$ with the sign factor attached to $a_0$ (trivial if $a_0=0$, the sign of $-(a_1a_2)^{-1}$ otherwise), times $2\pi$ times $\int_{y_1\in\mathbb R}\int_{y_2>0}\int_{x\in\mathbb R}$ of the Gaussian $\exp(-\pi(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2))$ times $a_1^2|y_1y_2|$ times the section factor $$y_1^{-n}\Bigl\{\bigl(-i\,a a_1a_2^{-1}xy_2/y_1\bigr)^{\delta}\bigl(a_2^{-2}(x^2/y_1^2-1/y_2^2-2ix/(y_1y_2))+a^2a_1^2y_2^2\bigr)+\tfrac{\delta}{\pi}a a_1a_2^{-1}(1+ixy_2/y_1)\Bigr\}$$ times $e^{-\pi a^2a_1^2y_2^2}$, times the quasi-character $|(y_1y_2)^{-1}|^{u_0+2}$ with sign factor for $a_0$ and the factor $|(y_1y_2)^{-1}|^{-2}$, times $e^{2\pi i a x}$, times $|y_2|^{c_2}$ with the central sign of $P_2$ and $|y_2|$, times $D.W\bigl(\mathrm{diag}(ay_1/y_2,1)\bigr)$, times $y_2^2|y_1y_2|^{-4}$, and finally times $|a_1a_2|^{s-1/2}$ and $a_1^{-2}$; elsewhere the integrand is $0$. On the right, $2\pi\,i^k\cdot\tfrac12\Gamma_{\mathbb R}(\tilde w+1)$ times $\int_{t\in\mathbb R}\int_{q\in\mathbb R}\int_{p>0}$ of the product of the pure sign characters attached to $s_P$ and $a_0$ at $-t$, to $1$ at $t$, and to $n \bmod 2$ and $a_0$ at $q$, times $W(-t)$, times $(p\,\mathrm{sgn}\,t)\bigl(a^2\,\mathrm{sgn}\,t\,(pq)^{-1}\bigr)^{\delta}$, times the bracket $-t^2p^2+a^2/p^2+\tfrac1{2\pi}-a^2/q^2+2a|t|p/q$, times $D.W\bigl(\mathrm{diag}(a|t|p/q,1)\bigr)$, times $|t|^{\,s-5/2-c_P-c_2}|q|^{\,u_0+c_P+c_2-2s-1}p^{\,u_0-c_2-3}$, times $e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$.
--
--   This is the unfolding of an archimedean Rankin–Selberg integral over a dual pair of torus coordinates into a threefold torus integral with an explicit $\Gamma_{\mathbb R}$-factor, for the section $\det^{\delta}$ times a block-quadratic form times a column harmonic of degree $n$ times a Gaussian. It follows by integrating the fibrewise identity [`LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic`](thm.html#LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic) against the general Fubini-plus-Gamma mechanism of [`LanglandsTunnell.Converse.setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre`](thm.html#LanglandsTunnell.Converse.setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre), and feeds the computation of the archimedean local factor as a root number times an explicit $\Gamma$-factor in the even principal series case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_blockQuadratic_colHarmonic_of_re_gt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell
open LanglandsTunnell.Converse
open MeasureTheory

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_blockQuadratic_colHarmonic_of_re_gt
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (s : ℂ)
    (hw : -1 < (2 * s - cP - P₂.centralExponent + n).re)
    (hIW : ∀ a₁ : ℝ, a₁ ≠ 0 → ∀ a₂ : ℝ, 0 < a₂ → Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n *
              ((-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ))) ^ δ *
                  ((a₂⁻¹ : ℂ) ^ 2 * ((((q.1 ^ 2 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 : ℝ)) : ℂ) - Complex.I * (((2 * q.1 / (q.2.1 * q.2.2) : ℝ)) : ℂ)) +
                    (a : ℂ) ^ 2 * (a₁ : ℂ) ^ 2 * (((q.2.2 ^ 2 : ℝ)) : ℂ)) +
                (δ : ℂ) / (Real.pi : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ)) * (1 + Complex.I * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ)))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))))
    (hK4 : Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-r.2.1) * ArchR.quasiChar 0 a₀ (-r.2.1) * ArchR.quasiChar 0 1 r.2.1 * ArchR.quasiChar 0 (n : ZMod 2) r.2.2.1 * ArchR.quasiChar 0 a₀ r.2.2.1) *
          (W (-r.2.1) * (((((r.2.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 r.2.1) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 r.2.1 * (((r.2.2.2 * r.2.2.1)⁻¹ : ℝ) : ℂ)) ^ δ) *
              (-(((r.2.1 : ℝ) : ℂ) ^ 2 * ((r.2.2.2 : ℝ) : ℂ) ^ 2) + (a : ℂ) ^ 2 * ((r.2.2.2⁻¹ : ℝ) : ℂ) ^ 2 + 1 / (2 * (Real.pi : ℂ)) - (a : ℂ) ^ 2 * ((r.2.2.1⁻¹ : ℝ) : ℂ) ^ 2 + 2 * (a : ℂ) * ((|r.2.1| : ℝ) : ℂ) * ((r.2.2.2 : ℝ) : ℂ) * ((r.2.2.1⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
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
            (((y₁⁻¹ : ℝ) : ℂ) ^ n *
              ((-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((x * y₂ / y₁ : ℝ)) : ℂ))) ^ δ *
                  ((a₂⁻¹ : ℂ) ^ 2 * ((((x ^ 2 / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ)) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ)) : ℂ)) +
                    (a : ℂ) ^ 2 * (a₁ : ℂ) ^ 2 * (((y₂ ^ 2 : ℝ)) : ℂ)) +
                (δ : ℂ) / (Real.pi : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ)) * (1 + Complex.I * (((x * y₂ / y₁ : ℝ)) : ℂ)))) *
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
          (W (-t) * (((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) *
              (-(((t : ℝ) : ℂ) ^ 2 * ((p : ℝ) : ℂ) ^ 2) + (a : ℂ) ^ 2 * ((p⁻¹ : ℝ) : ℂ) ^ 2 + 1 / (2 * (Real.pi : ℂ)) - (a : ℂ) ^ 2 * ((q⁻¹ : ℝ) : ℂ) ^ 2 + 2 * (a : ℂ) * ((|t| : ℝ) : ℂ) * ((p : ℝ) : ℂ) * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) := by sorry
