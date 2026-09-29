-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_conjBlock
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_conjBlock
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/9f4c0f12-7b49-5c84-bb23-8b809c097106
-- title:
--   Fibrewise Iwasawa identity for the conjugate-block flat section
-- statement:
--   Fix a real archimedean parameter $P_2$ (either a principal pair $(u_1,a_1,u_2,a_2)$ or a discrete parameter $(u,k)$ with $k\ge 1$), with central exponent $c(P_2)$ equal to $u_1+u_2$, resp. $2u$; fix an archimedean datum $D$ for $P_2$, i.e. a smooth Whittaker function $D.W$ on $2\times2$ real matrices satisfying the unipotent law with respect to $\psi(x)=e^{2\pi i x}$, the central law with respect to the central quasicharacter of $P_2$, and the stated analytic properties of its zeta integrals. Fix further a function $W:\mathbb R\to\mathbb C$, reals $a$, $a_1\neq 0$ and $a_2>0$, complex numbers $u_0$, $c_P$, $s$, classes $a_0,s_P\in\mathbb Z/2$, an integer $k$ and a natural number $n$. Here $\mathrm{quasiChar}(u,\varepsilon,y)=|y|^{u}$ if $\varepsilon=0$ and $|y|^{u}\,\mathrm{sgn}(y)$ otherwise, and $\mathrm{diagOne}(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix}$. The assertion is the equality of two explicit complex numbers. The left-hand side is
--   $$|a_1a_2|\cdot i^{k}\,|{-a_1^{-1}}|^{c_P+1}\Bigl(\tfrac{-a_1^{-1}}{|-a_1^{-1}|}\Bigr)^{s_P}W(-a_1/a_2)\cdot \mathrm{quasiChar}(u_0+1,a_0,-(a_1a_2)^{-1})\cdot 2\pi\,\mathcal I\cdot |a_1a_2|^{s-1/2}\cdot a_1^{-2},$$
--   where $\mathcal I$ is the iterated integral over $y_1\in\mathbb R$, $y_2\in(0,\infty)$, $x\in\mathbb R$ of
--   $$e^{-\pi(a_2^{-2}(x^2/y_1^2+y_2^{-2})+y_1^{-2})}\,a_1^2|y_1y_2|\,y_1^{-n}\bigl(-a a_1 y_2-a_2^{-1}y_2^{-1}+i a_2^{-1}x/y_1\bigr)e^{-\pi a^2a_1^2y_2^2}$$
--   times $\mathrm{quasiChar}(u_0+2,a_0,(y_1y_2)^{-1})\,|(y_1y_2)^{-1}|^{-2}$, times $\psi(ax)$, the central quasicharacter of $P_2$ at $y_2$ times $|y_2|$, $D.W(\mathrm{diagOne}(ay_1/y_2))$, and $y_2^2|y_1y_2|^{-4}$. The right-hand side is $2\pi\,i^{k}a_2^{-1}$ times the iterated integral over $q\in\mathbb R$, $p\in(0,\infty)$ of
--   $$a_2^{\,2s-c_P-c(P_2)+n}e^{-\pi a_2^2q^2}\cdot\mathrm{quasiChar}(0,s_P,-a_1/a_2)\,\mathrm{quasiChar}(0,a_0,-a_1/a_2)\,\mathrm{quasiChar}(0,1,a_1/a_2)\,\mathrm{quasiChar}(0,n\bmod 2,q)\,\mathrm{quasiChar}(0,a_0,q)$$
--   times $W(-a_1/a_2)\bigl(-(a+(a_1/a_2)p^2+a\,p\,\mathrm{quasiChar}(0,1,a_1/a_2)q^{-1})\bigr)D.W(\mathrm{diagOne}(a|a_1/a_2|p/q))$, times $|a_1/a_2|^{\,s-5/2-c_P-c(P_2)}|q|^{u_0+n}p^{\,u_0-c(P_2)-3}$, times $e^{-\pi(a_1/a_2)^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$. No integrability hypothesis is imposed.
--
--   This is the fibrewise form, at a fixed pair $(a_1,a_2)$ with $a_1\neq 0<a_2$, of the substitution identity that converts the unfolded three-variable Iwasawa-coordinate integral attached to the conjugate-block flat section of weight $n+1$ into a two-variable integral over $(q,p)$ in the variable $t=a_1/a_2$. It is used by [`LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_conjBlock_of_re_gt`](thm.html#LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_conjBlock_of_re_gt), where the fibrewise equality is integrated over the dual torus in a right half-plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_conjBlock.lean

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

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_conjBlock
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (n : ℕ) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂) :
    (((((|a₁ * a₂| : ℝ) : ℂ) *
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
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ))
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ) *
        ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
        (((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * (-((a : ℂ) + ((a₁ / a₂ : ℝ) : ℂ) * (p : ℂ) ^ 2 + (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + n)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) := by sorry
