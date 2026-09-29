-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile
-- name    : LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/0f8c01b8-19b0-5247-894e-d237278f894a
-- title:
--   Dual torus-triple evaluation, conjugate block, discrete branch
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb{C}$ and $a_1\neq a_2$ in $\mathbb{Z}/2$, and let $W:\mathbb{R}\to\mathbb{C}$ be continuous on $\{t\neq 0\}$ and satisfy the two-sheet Gaussian-convolution law: for every $b\in\mathbb{Z}/2$ and every $t>0$, $W(t)+(-1)^{b}W(-t)=t\cdot\bigl(4\int_0^\infty r^{\nu_1+[a_1+b]}e^{-\pi r^2}(t/r)^{\nu_2+[a_2+b]}e^{-\pi (t/r)^2}\,dr/r\bigr)$, where $[c]=\mathrm{signShift}(c)$ is $0$ for $c=0$ and $1$ otherwise. Let $u\in\mathbb{C}$, $k\geq 1$, let $D$ be a real archimedean Whittaker datum for the parameter $P_2$ (a function on $2\times2$ real matrices with the smoothness, unipotent and central transformation laws, zeta integrals factoring through the archimedean $\Gamma$-factor, functional equation, finite order and decay conditions of `ArchDatumR`), with $P_2=\mathrm{discrete}\,(u,k)$, so that $P_2$'s central exponent is $2u$. Assume $D$ has the one-sided discrete profile of constant $\rho$: $D.W(\mathrm{diag}(\tau,1))=\rho\cdot 2\tau^{u+k/2+1}e^{-2\pi\tau}$ and $D.W(\mathrm{diag}(-\tau,1))=0$ for all $\tau>0$. Put $a=-1$, $c_P=\nu_1+\nu_2$, $s_P=a_1+a_2$, $n=k$, and let $u_0\in\mathbb{C}$, $a_0\in\mathbb{Z}/2$ be arbitrary. Then there is $\sigma\in\mathbb{R}$ such that for all $s$ with $\operatorname{Re}s>\sigma$, $\Gamma_{\mathbb{R}}(2s-c_P-c_2+n+1)$ times the iterated integral over $t\in\mathbb{R}$, $q\in\mathbb{R}$, $p\in(0,\infty)$ (innermost in $p$) of $$\chi_{s_P}(-t)\chi_{a_0}(-t)\chi_{1}(t)\chi_{[n]}(q)\chi_{a_0}(q)\,W(-t)\bigl(-(a+tp^2+a\,p\,\chi_1(t)q^{-1})\bigr)D.W(\mathrm{diag}(a|t|p/q,1))\,|t|^{s-5/2-c_P-c_2}|q|^{u_0+c_P+c_2-2s-1}p^{u_0-c_2-3}e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$$ equals $(-1)^{a_0+1+k}\rho\cdot\tfrac12\cdot\Gamma_{\mathbb{R}}(s+\tfrac12+(-\nu_1-u_0)+[a_1+a_0])\,\Gamma_{\mathbb{R}}(s+\tfrac12+(-\nu_2-u_0)+[a_2+a_0])$ times $\prod_{i=1,2}\Gamma_{\mathbb{R}}(s+\tfrac12-\nu_i-u+\tfrac k2)\Gamma_{\mathbb{R}}(s+\tfrac12-\nu_i-u+\tfrac k2+1)$. Here $\chi_c(y)=\mathrm{quasiChar}\,0\,c\,y$ is the sign character attached to $c$, and $c_2$ denotes the central exponent of $P_2$.
--
--   This is the evaluation, in a right half-plane, of the archimedean torus triple integral occurring on the dual (contragredient) side of the $GL(3)\times GL(2)$ Rankin–Selberg pair for the conjugate-block section, with the Levi parameter on the discrete-series branch: after multiplication by the outer $\Gamma_{\mathbb{R}}$-factor it becomes an explicit constant times a product of six $\Gamma_{\mathbb{R}}$-factors, the last four of which combine into two $\Gamma_{\mathbb{C}}$-factors. It feeds the comparison of the dual torus pair with the archimedean root number and $\gamma$-factor used in the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile.lean

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

theorem LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u : ℂ) (k : ℕ) (hk : 1 ≤ k) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.discrete u k hk)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = a₁ + a₂) (n : ℕ) (hn : n = k) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * (-((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 + (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (a₀.val + 1 + k) * ρ * (1 / 2 : ℂ) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (a₁ + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (a₂ + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2))) *
            Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (k : ℂ) / 2)) + 1)) *
            (Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2))) *
              Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (k : ℂ) / 2)) + 1)))) := by sorry
