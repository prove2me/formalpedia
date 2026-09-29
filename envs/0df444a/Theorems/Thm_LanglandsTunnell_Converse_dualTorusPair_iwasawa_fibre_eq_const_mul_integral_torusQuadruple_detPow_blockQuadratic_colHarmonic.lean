-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/41796e8e-74d1-5e29-a474-0d98f1879669
-- title:
--   Fibrewise quadratic identity for the dual torus pair
-- statement:
--   Fix a real archimedean parameter $P_2$ (principal, given by exponents $u_1,u_2$ and signs, or discrete of weight $k\ge 1$), an archimedean Whittaker datum $D$ for $P_2$ (a smooth function $D.W$ on $2\times 2$ real matrices transforming by $x\mapsto e^{2\pi i x}$ under the unipotent, by the central quasi-character of $P_2$ under scalars, with the prescribed zeta integrals, functional equation and decay), an arbitrary function $W:\mathbb{R}\to\mathbb{C}$, reals $a$, $a_1\neq 0$ and $a_2>0$, complex parameters $u_0,c_P,s$, signs $a_0,s_P\in\mathbb{Z}/2$, an integer $k$, a natural number $n$, and $\delta$ with $\delta=0$ or $\delta=1$. The asserted identity equates two complex numbers. On the left stands the fixed-$(a_1,a_2)$ fibre of the unfolded dual torus pair in Iwasawa form: the product of $|a_1a_2|$, $i^k$, $|a_1^{-1}|^{c_P+1}$, the sign factor $(-a_1^{-1}/|a_1^{-1}|)^{s_P}$, $W(-a_1/a_2)$, the quasi-character $|{-}(a_1a_2)^{-1}|^{u_0+1}$ times its sign when $a_0\neq 0$, $|a_1a_2|^{s-1/2}$, $a_1^{-2}$, and $2\pi$ times the triple integral over $y_1\in\mathbb{R}$, $y_2\in(0,\infty)$, $x\in\mathbb{R}$ of a Gaussian integrand carrying the factor $y_1^{-n}$, the $\delta$-th power of $-i\,a a_1a_2^{-1}xy_2/y_1$ times a block quadratic in $x/y_1,1/y_2,y_2$ together with its $\delta/\pi$ correction term, quasi-character and central-character weights in $y_1y_2$ and $y_2$, the additive character $e^{2\pi i a x}$, the Whittaker value $D.W(\mathrm{diag}(ay_1/y_2,1))$, and the determinant power $y_2^2|y_1y_2|^{-4}$. On the right stands $2\pi\, i^k a_2^{-1}$ times the double integral over $q\in\mathbb{R}$, $p\in(0,\infty)$ of $a_2^{2s-c_P-\mathrm{cex}(P_2)+n}e^{-\pi a_2^2q^2}$ times sign quasi-characters in $-a_1/a_2$ and $q$, $W(-a_1/a_2)$, the kernel $p\cdot\bigl(a^2(pq)^{-1}\bigr)^{\delta}$ with its sign twists, the bracket $-(a_1/a_2)^2p^2+a^2p^{-2}+\tfrac1{2\pi}-a^2q^{-2}+2a|a_1/a_2|p\,q^{-1}$, the Whittaker value $D.W(\mathrm{diag}(a|a_1/a_2|p/q,1))$, the powers $|a_1/a_2|^{s-5/2-c_P-\mathrm{cex}(P_2)}$, $|q|^{u_0+n}$, $p^{u_0-\mathrm{cex}(P_2)-3}$, and the three Gaussians $e^{-\pi(a_1/a_2)^2p^2}$, $e^{-\pi a^2/p^2}$, $e^{-\pi a^2/q^2}$, where $\mathrm{cex}(P_2)$ denotes the central exponent of $P_2$. No integrability hypothesis is imposed.
--
--   This is the pointwise, fixed-$(a_1,a_2)$ fibre of the archimedean computation attached to the quadratic section in the converse-theorem input for the Langlands–Tunnell argument: the triple $(y_1,y_2,x)$ integral is reduced, after the quadratic and cubic $x$-moment evaluations and two one-variable substitutions, to a $(q,p)$ integral whose kernel is the product of the $\delta$-factor and the block quadratic $B^Q$. It is cited by the integrated form [`LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_blockQuadratic_colHarmonic_of_re_gt`](thm.html#LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_blockQuadratic_colHarmonic_of_re_gt), where the fibres are assembled over the torus variables under a half-plane condition on $\operatorname{Re} s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic.lean

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

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (s : ℂ)
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
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ))
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ) *
        ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
        (((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * (((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂)) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 (a₁ / a₂) * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) *
              (-((((a₁ / a₂) : ℝ) : ℂ) ^ 2 * ((p : ℝ) : ℂ) ^ 2) + (a : ℂ) ^ 2 * ((p⁻¹ : ℝ) : ℂ) ^ 2 + 1 / (2 * (Real.pi : ℂ)) - (a : ℂ) ^ 2 * ((q⁻¹ : ℝ) : ℂ) ^ 2 + 2 * (a : ℂ) * ((|(a₁ / a₂)| : ℝ) : ℂ) * ((p : ℝ) : ℂ) * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + n)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) := by sorry
