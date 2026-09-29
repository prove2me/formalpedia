-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_minor
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_minor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/3a2289fa-1cf3-5d7c-bb61-b328df836803
-- title:
--   Fibre identity for the dual torus pair integral
-- statement:
--   Fix a real archimedean parameter $P_2$ (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$, with central exponent $u_1+u_2$, or $\mathrm{discrete}(u,k)$, with central exponent $2u$), write $c_2=P_2.\mathrm{centralExponent}$, and let $D$ be an `ArchDatumR P₂`, i.e. a Whittaker function $D.W$ on $2\times 2$ real matrices, smooth on the invertible locus, satisfying $D.W(\mathrm{unip}(x)g)=\psi(x)D.W(g)$ with $\psi(x)=e^{2\pi i x}$ and $D.W(zg)=\mathrm{centralChar}_{P_2}(z)|z|\,D.W(g)$ for $z\neq0$, together with the attached entire zeta functions, functional equation and growth and decay estimates. Let $W:\mathbb R\to\mathbb C$ be an arbitrary function, $a,a_1,a_2$ real with $a_1\neq0$ and $a_2>0$, $u_0,c_P,s\in\mathbb C$, $a_0,s_P\in\mathbb Z/2$ and $k\in\mathbb Z$. Here $\mathrm{quasiChar}(u,\epsilon,y)=|y|^{u}$ times $1$ if $\epsilon=0$ and $\mathrm{sign}(y)$ otherwise, $\mathrm{centralChar}_{P_2}(y)=\mathrm{quasiChar}(c_2,P_2.\mathrm{centralSign},y)$, and $\mathrm{diagOne}(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix}$. The asserted equality identifies two complex numbers. On the left stands $|a_1a_2|\cdot i^{k}\,|{-a_1^{-1}}|^{c_P+1}\bigl((-a_1^{-1})/|{-a_1^{-1}}|\bigr)^{s_P.\mathrm{val}}\,W(-a_1/a_2)\cdot \mathrm{quasiChar}(u_0+1,a_0,-(a_1a_2)^{-1})\cdot|a_1a_2|^{s-1/2}\cdot a_1^{-2}$ times $2\pi$ times the iterated integral over $y_1\in\mathbb R$, $y_2\in(0,\infty)$, $x\in\mathbb R$ of the Gaussian $e^{-\pi(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2)}$ times $a_1^2|y_1y_2|$, times $\bigl(-iaa_1(-(y_2/y_1))+ia_2^{-1}(y_1y_2)^{-1}\bigr)$, times $e^{-\pi a^2a_1^2y_2^2}$, times $\mathrm{quasiChar}(u_0+2,a_0,(y_1y_2)^{-1})\,|(y_1y_2)^{-1}|^{-2}$, times $\psi(ax)\,\mathrm{centralChar}_{P_2}(y_2)|y_2|\,D.W(\mathrm{diagOne}(ay_1/y_2))$, times $y_2^2|y_1y_2|^{-4}$. On the right stands $2\pi\, i^{k}\, i\, a_2^{-1}$ times the iterated integral over $q\in\mathbb R$, $p\in(0,\infty)$ of $a_2^{\,2s-c_P-c_2+1}e^{-\pi a_2^2q^2}$ times the product of the sign characters $\mathrm{quasiChar}(0,s_P,-a_1/a_2)\mathrm{quasiChar}(0,a_0,-a_1/a_2)\mathrm{quasiChar}(0,1,a_1/a_2)\mathrm{quasiChar}(0,1,q)\mathrm{quasiChar}(0,a_0,q)$, of $W(-(a_1/a_2))\,(a+(a_1/a_2)p^2)\,D.W(\mathrm{diagOne}(a|a_1/a_2|p/q))$, of $|a_1/a_2|^{\,s-5/2-c_P-c_2}|q|^{u_0+1}p^{\,u_0-c_2-3}$, and of $e^{-\pi(a_1/a_2)^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$. No integrability hypothesis is imposed.
--
--   This is the pointwise fibre computation, at a fixed pair $(a_1,a_2)$ with $a_1\neq 0<a_2$, underlying the minor-section evaluation of the dual Iwasawa integral in the archimedean converse step: the inner $x$-integration is a Gaussian Fourier transform and the torus variables are rewritten by the substitutions $y_1=1/(a_2q)$, $y_2=1/(|a_1|p)$. It is used by [`LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_minor_of_re_gt`](thm.html#LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_minor_of_re_gt), where the remaining Jacobian in passing from $(a_1,a_2)$ to $(a_2,a_1/a_2)$ accounts for the factor $a_2^{-1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_minor.lean

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

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_minor
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (s : ℂ)
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
            (-Complex.I * (a : ℂ) * (a₁ : ℂ) * ((-(y₂ / y₁) : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((y₁ * y₂)⁻¹ : ℝ) : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ))
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * Complex.I * (((a₂⁻¹ : ℝ)) : ℂ) *
        ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
        (((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((a : ℂ) + ((a₁ / a₂ : ℝ) : ℂ) * (p : ℂ) ^ 2) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) := by sorry
