-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_colHarmonic_of_re_gt
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_colHarmonic_of_re_gt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/66123799-21b3-51cf-8e2c-f07b8b0f2570
-- title:
--   Iwasawa-unfolded dual torus pair as a torus-triple integral
-- statement:
--   Fix a real archimedean parameter $P_2$ (so $c_2:=$ `P₂.centralExponent` is $u_1+u_2$ in the principal case and $2u$ in the discrete case), an archimedean Whittaker datum $D$ for $P_2$ with associated function $D.W$ on $2\times 2$ real matrices, a function $W:\mathbb R\to\mathbb C$, a real number $a$, complex parameters $u_0,c_P$, signs $a_0,s_P\in\mathbb Z/2$, an integer $k$, natural numbers $n$ and $\delta$ with $\delta\in\{0,1\}$, and $s\in\mathbb C$. Assume the abscissa condition $-1<\operatorname{Re}(2s-c_P-c_2+n)$, the integrability hypothesis `hIW` stating that for every $a_1\neq 0$ and $a_2>0$ the inner Iwasawa integrand in the variables $(x,y_1,y_2)$ is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$ for Lebesgue measure, and the integrability hypothesis `hK4` for the corresponding four-variable integrand in $(a_2,t,q,p)$ on $(0,\infty)\times\mathbb R\times\mathbb R\times(0,\infty)$. Then the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb R$ of the integrand which, for $a_1\neq 0$ and $a_2>0$, equals $|a_1a_2|\cdot\bigl(i^{k}\,|{-a_1^{-1}}|^{c_P+1}\,((-a_1^{-1})/|{-a_1^{-1}}|)^{s_P}\,W(-a_1/a_2)\bigr)\cdot\bigl(\mathrm{quasiChar}(u_0+1,a_0,-(a_1a_2)^{-1})\cdot 2\pi\int_{y_1}\int_{y_2>0}\int_x(\cdots)\bigr)\cdot|a_1a_2|^{s-1/2}\cdot a_1^{-2}$ and vanishes otherwise — the inner triple integrand being the product of Gaussians $\exp(-\pi(a_2^{-2}(x^2/y_1^2+y_2^{-2})+y_1^{-2}))$ and $\exp(-\pi a^2a_1^2y_2^2)$, the section factor $a_1^2|y_1y_2|\,y_1^{-n}(-i\,a a_1a_2^{-1}xy_2/y_1)^{\delta}$, the quasicharacter $\mathrm{quasiChar}(u_0+2,a_0,(y_1y_2)^{-1})|(y_1y_2)^{-1}|^{-2}$, the additive character $\psi(ax)=\exp(2\pi i a x)$, the central quasicharacter $\mathrm{centralChar}(P_2,y_2)|y_2|$, the value $D.W$ at $\mathrm{diag}(ay_1/y_2,1)$ and the Jacobian $y_2^2|y_1y_2|^{-4}$ — equals $\bigl(2\pi\,i^{k}\cdot\tfrac12\Gamma_{\mathbb R}(2s-c_P-c_2+n+1)\bigr)$ times the iterated integral over $t\in\mathbb R$, $q\in\mathbb R$, $p\in(0,\infty)$ of the product of the sign characters $\mathrm{quasiChar}(0,s_P,-t)\,\mathrm{quasiChar}(0,a_0,-t)\,\mathrm{sgn}(t)\,\mathrm{quasiChar}(0,n\bmod 2,q)\,\mathrm{quasiChar}(0,a_0,q)$, the factor $W(-t)\,\bigl(p\,\mathrm{sgn}(t)\bigr)\bigl(a^2\,\mathrm{sgn}(t)(pq)^{-1}\bigr)^{\delta}D.W(\mathrm{diag}(a|t|p/q,1))$, the powers $|t|^{s-5/2-c_P-c_2}|q|^{u_0+c_P+c_2-2s-1}p^{u_0-c_2-3}$, and $\exp(-\pi t^2p^2)\exp(-\pi a^2/p^2)\exp(-\pi a^2/q^2)$.
--
--   This is one step in the archimedean computation of the dual (Weyl-translated) torus integral for the $\det^{\delta}\cdot(\text{column harmonic})^{n}\cdot\text{Gaussian}$ test section: the two outer torus variables are integrated out, the $a_2$-integration producing a real Gamma factor $\tfrac12\Gamma_{\mathbb R}(2s-c_P-c_2+n+1)$ and the shift of the exponent of $|q|$, leaving a triple integral over $(t,q,p)$. It feeds the three archimedean root-number identities for the even principal series profiles used in the Rankin–Selberg side of the converse-theorem argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_colHarmonic_of_re_gt.lean

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

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_colHarmonic_of_re_gt
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (s : ℂ)
    (hw : -1 < (2 * s - cP - P₂.centralExponent + n).re)
    (hIW : ∀ a₁ : ℝ, a₁ ≠ 0 → ∀ a₂ : ℝ, 0 < a₂ → Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))))
    (hK4 : Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-r.2.1) * ArchR.quasiChar 0 a₀ (-r.2.1) * ArchR.quasiChar 0 1 r.2.1 * ArchR.quasiChar 0 (n : ZMod 2) r.2.2.1 * ArchR.quasiChar 0 a₀ r.2.2.1) *
          (W (-r.2.1) * ((((r.2.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 r.2.1) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 r.2.1 * (((r.2.2.2 * r.2.2.1)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |r.2.1| * r.2.2.2 / r.2.2.1))) *
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
            (((y₁⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((x * y₂ / y₁ : ℝ)) : ℂ))) ^ δ) *
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
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) := by sorry
