-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_blockHarmonic
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_blockHarmonic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/116f0f1a-6e06-5c4a-925c-d814eaeb0aa4
-- title:
--   Fixed (a₁,a₂) fibre of the major dual torus pair
-- statement:
--   Fix a real archimedean parameter $P_2$ (either principal, with data $(u_1,\epsilon_1,u_2,\epsilon_2)$, or discrete, with data $(u,k_0)$), an archimedean Whittaker datum $D$ for $P_2$ (a function $D.W$ on real $2\times 2$ matrices subject to the unipotent and central transformation laws, smoothness, the zeta-integral, functional-equation, finite-order and decay conditions of `ArchDatumR`), a function $W\colon\mathbb R\to\mathbb C$, a real number $a$, complex parameters $u_0,c_P,s$, classes $\epsilon_0,s_P\in\mathbb Z/2$, an integer $k$, and reals $a_1\neq 0$, $a_2>0$. Throughout, $\mathrm{quasiChar}(u,\epsilon,y)=|y|^{u}$ times $1$ if $\epsilon=0$ and $\mathrm{sgn}(y)$ otherwise, $\mathrm{psi}(x)=e^{2\pi i x}$, $\mathrm{centralChar}(P_2,\cdot)$ is the quasicharacter attached to the central exponent and sign of $P_2$, and $\mathrm{diagOne}(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix}$. The assertion is an identity of complex numbers. On the left stands the product of $|a_1a_2|$, of $i^{k}\,\bigl(|{-a_1^{-1}}|^{c_P+1}\bigr)\bigl((-a_1^{-1})/|{-a_1^{-1}}|\bigr)^{s_P}\,W(-a_1/a_2)$, of $\mathrm{quasiChar}(u_0+1,\epsilon_0,-(a_1a_2)^{-1})$ times $2\pi$ times the iterated integral over $y_1\in\mathbb R$, $y_2\in(0,\infty)$, $x\in\mathbb R$ of $$e^{-\pi\left(a_2^{-2}(x^2/y_1^2+y_2^{-2})+y_1^{-2}\right)}a_1^2|y_1y_2|\,\frac1{y_1}\Bigl(aa_1y_2+\frac1{a_2y_2}+\frac{ix}{a_2y_1}\Bigr)e^{-\pi a^2a_1^2y_2^2}\cdot \mathrm{quasiChar}(u_0+2,\epsilon_0,(y_1y_2)^{-1})\,|(y_1y_2)^{-1}|^{-2}\cdot e^{2\pi i a x}\,\mathrm{centralChar}(P_2,y_2)|y_2|\,D.W(\mathrm{diagOne}(ay_1/y_2))\cdot y_2^2|y_1y_2|^{-4},$$ of $|a_1a_2|^{s-1/2}$ and of $a_1^{-2}$. On the right stands $2\pi\,i^{k}\,a_2^{-1}$ times the iterated integral over $q\in\mathbb R$, $p\in(0,\infty)$ of $a_2^{2s-c_P-c(P_2)+1}e^{-\pi a_2^2q^2}$ times the sign factors $\mathrm{quasiChar}(0,s_P,-t)\,\mathrm{quasiChar}(0,\epsilon_0,-t)\,\mathrm{quasiChar}(0,1,t)\,\mathrm{quasiChar}(0,1,q)\,\mathrm{quasiChar}(0,\epsilon_0,q)$ with $t=a_1/a_2$, times $W(-t)\bigl(a+tp^2-ap\,\mathrm{quasiChar}(0,1,t)\,q^{-1}\bigr)D.W(\mathrm{diagOne}(a|t|p/q))$, times $|t|^{s-5/2-c_P-c(P_2)}|q|^{u_0+1}p^{u_0-c(P_2)-3}$, times $e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$, where $c(P_2)$ is the central exponent of $P_2$. No integrability hypothesis is imposed; both sides are iterated Bochner integrals.
--
--   This is the pointwise, fixed-$(a_1,a_2)$ fibre of the block-harmonic (major) dual torus computation in the archimedean converse-theorem argument: it converts the three-variable Iwasawa-coordinate integral attached to the datum $D$, with its $\theta$-free section bracket, into the two-variable $(q,p)$ integral in the torus variable $t=a_1/a_2$, the Gaussian moment in $x$ producing the extra term $-ap\,\mathrm{sgn}(t)/q$ in the bracket. It is used in [`LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_blockHarmonic_of_re_gt`](thm.html#LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_blockHarmonic_of_re_gt), where the outer integration over $(a_1,a_2)$ is performed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_blockHarmonic.lean

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

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_blockHarmonic
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
            (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ))
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ) *
        ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
        (((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((a : ℂ) + ((a₁ / a₂ : ℝ) : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) := by sorry
