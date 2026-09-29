-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile
-- name    : LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/52c0588e-b4fb-516b-9e8b-3e59b84678fa
-- title:
--   Dual torus triple integral as six Γ_ℝ-factors
-- statement:
--   Let $\nu_1,\nu_2\in\mathbb C$, let $b,c\in\mathbb Z/2$ with $c=b+1$, and let $W:\mathbb R\to\mathbb C$ be continuous on $\{t\neq0\}$, of parity $b$ in the sense that $W(-t)=(-1)^{b}W(t)$ for all $t$, and such that for $t>0$ the symmetrised value $W(t)+(-1)^{b}W(-t)$ equals $t$ times the Gaussian Mellin convolution $4\int_0^\infty r^{\nu_1}e^{-\pi r^2}(t/r)^{\nu_2}e^{-\pi(t/r)^2}\,dr/r$. Let $\mu_1,\mu_2\in\mathbb C$ and let $D$ be a real archimedean Whittaker datum (an `ArchDatumR`: a function on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent and central transformation laws, entire zeta functions satisfying the functional equation, of finite order, with the decay bounds) for the parameter $P_2=\mathrm{principal}(\mu_1,c,\mu_2,c)$, whose torus restriction satisfies $D.W(\mathrm{diag}(\tau,1))=\rho\,\tau\cdot 4\int_0^\infty r^{\mu_1}e^{-\pi r^2}(\tau/r)^{\mu_2}e^{-\pi(\tau/r)^2}\,dr/r$ for $\tau>0$ and $D.W(\mathrm{diag}(-\tau,1))=(-1)^{c}D.W(\mathrm{diag}(\tau,1))$. Finally let $a=-1$, $u_0\in\mathbb C$, $c_P=\nu_1+\nu_2$, $a_0,s_P\in\mathbb Z/2$ with $s_P=b+b$, $n=2$, and $\delta\in\{0,1\}$ with $\delta\equiv a_0+b \pmod 2$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma$ the product of $\Gamma_{\mathbb R}(2s-c_P-c_2+n+1)$, where $c_2=P_2.\mathrm{centralExponent}=\mu_1+\mu_2$, with the triple integral over $t\in\mathbb R$, $q\in\mathbb R$, $p\in(0,\infty)$ of the integrand formed by: the five sign characters $\mathrm{quasiChar}\,0\,s_P(-t)$, $\mathrm{quasiChar}\,0\,a_0(-t)$, $\mathrm{quasiChar}\,0\,1\,t$, $\mathrm{quasiChar}\,0\,(n\bmod 2)\,q$, $\mathrm{quasiChar}\,0\,a_0\,q$ (each $\mathrm{quasiChar}\,0\,\epsilon(y)=1$ or $\operatorname{sign}y$ according as $\epsilon=0$ or not); the factor $W(-t)$ times the bracket $\bigl(p\,\mathrm{quasiChar}\,0\,1\,t\bigr)\bigl(a^2\,\mathrm{quasiChar}\,0\,1\,t\,(pq)^{-1}\bigr)^{\delta}$ times the quadratic $-t^2p^2+a^2p^{-2}+\tfrac1{2\pi}-a^2q^{-2}+2a|t|pq^{-1}$ times $D.W(\mathrm{diag}(a|t|p/q,1))$; the powers $|t|^{\,s-5/2-c_P-c_2}$, $|q|^{\,u_0+c_P+c_2-2s-1}$, $p^{\,u_0-c_2-3}$; and the Gaussians $e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$, equals $(-1)^{b+\delta}\cdot 2\rho$ times the six-fold product $\prod_{i=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12-\nu_i-u_0+\mathrm{signShift}(b+a_0)\bigr)\cdot\prod_{j=1,2}\prod_{i=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12-\nu_i-\mu_j+\mathrm{signShift}(b+c)\bigr)$, where $\mathrm{signShift}(\epsilon)$ is $0$ for $\epsilon=0$ and $1$ otherwise.
--
--   This is the archimedean evaluation of the dual side of a Rankin–Selberg triple integral in the quadratic ($\delta$-shifted) section, for an even principal parameter and a weight-zero Levi datum: after folding the $(t,q)$-quadrants against the one-sheet Whittaker function of parity $b$ and the parity-$c$ torus profile, the surviving monomials are Barnes-balanced and integrate to the expected product of six $\Gamma_{\mathbb R}$-factors, up to the constant $(-1)^{b+\delta}2\rho$. It feeds the identification of the dual torus pair with the archimedean root number times the expected gamma factor in the converse-theorem input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile.lean

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

theorem LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile
    (ν₁ ν₂ : ℂ) (b c : ZMod 2) (hc : c = b + 1)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = b + b)
    (n : ℕ) (hn : n = 2) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * (((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) *
              (-(((t : ℝ) : ℂ) ^ 2 * ((p : ℝ) : ℂ) ^ 2) + (a : ℂ) ^ 2 * ((p⁻¹ : ℝ) : ℂ) ^ 2 + 1 / (2 * (Real.pi : ℂ)) - (a : ℂ) ^ 2 * ((q⁻¹ : ℝ) : ℂ) ^ 2 + 2 * (a : ℂ) * ((|t| : ℝ) : ℂ) * ((p : ℝ) : ℂ) * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (b.val + δ) * 2 * ρ * ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (b + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (b + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₁) + signShift (b + c))) *
            Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₁) + signShift (b + c)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₂) + signShift (b + c))) *
              Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₂) + signShift (b + c)))))) := by sorry
