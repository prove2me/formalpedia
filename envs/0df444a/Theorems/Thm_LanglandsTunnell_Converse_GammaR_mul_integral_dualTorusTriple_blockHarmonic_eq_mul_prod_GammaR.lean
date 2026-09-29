-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR
-- name    : LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/73ad81c2-5063-5139-a7cc-43483c56bee0
-- title:
--   Dual torus-triple evaluation for the block-harmonic section
-- statement:
--   Let $\nu_1,\nu_2\in\mathbb C$, let $a_1,a_2,c\in\mathbb Z/2$ with $a_1\neq a_2$, and let $W:\mathbb R\to\mathbb C$ be continuous on $\{t\neq0\}$ and satisfy, for every $b\in\mathbb Z/2$ and every $t>0$, the two-sheet identity $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_0^\infty r^{\nu_1+[a_1+b]}e^{-\pi r^2}(t/r)^{\nu_2+[a_2+b]}e^{-\pi(t/r)^2}\,dr/r$, where $[a]=0$ for $a=0$ and $[a]=1$ otherwise (`signShift`). Let $\mu_1,\mu_2\in\mathbb C$, let $D$ be a real archimedean Whittaker datum (the structure `ArchDatumR`, comprising a function on $2\times2$ real matrices that is smooth on the invertible locus, unipotent-equivariant by $\psi$, transforms by the central character, together with its entire zeta functions, functional equation, finite-order and decay data) for a parameter $P_2$ equal to $\mathrm{principal}(\mu_1,c,\mu_2,c)$, so $P_2$'s central exponent is $\mu_1+\mu_2$, and let $\rho\in\mathbb C$ be such that $D.W(\mathrm{diag}(\tau,1))=\rho\,\tau\cdot 4\int_0^\infty r^{\mu_1}e^{-\pi r^2}(\tau/r)^{\mu_2}e^{-\pi(\tau/r)^2}\,dr/r$ for $\tau>0$, and $D.W(\mathrm{diag}(-\tau,1))=(-1)^{c}D.W(\mathrm{diag}(\tau,1))$ for $\tau>0$. Finally let $a=-1$, let $u_0\in\mathbb C$, let $c_P=\nu_1+\nu_2$, and let $a_0=c$, $s_P=a_1+a_2$ in $\mathbb Z/2$. Then there is $\sigma\in\mathbb R$ such that for all $s$ with $\sigma<\operatorname{Re}s$, the product of $\Gamma_{\mathbb R}(2s-c_P-P_2.\mathrm{centralExponent}+2)$ with the iterated integral over $t\in\mathbb R$, $q\in\mathbb R$, $p\in(0,\infty)$ of the sign factor $\mathrm{sgn}(-t)^{s_P}\mathrm{sgn}(-t)^{a_0}\mathrm{sgn}(t)\mathrm{sgn}(q)\mathrm{sgn}(q)^{a_0}$ (each written as `ArchR.quasiChar 0 · ·` at exponent $0$) times $W(-t)\bigl(a+tp^2-ap\,\mathrm{sgn}(t)q^{-1}\bigr)D.W(\mathrm{diag}(a|t|p/q,1))$ times $|t|^{s-5/2-c_P-c_2}|q|^{u_0+c_P+c_2-2s-1}p^{u_0-c_2-3}$ (with $c_2=P_2.\mathrm{centralExponent}$) times $e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$, equals $(-1)^{c}\rho$ times the six-fold product $\prod_{i=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12-\nu_i-u_0+[a_i+c]\bigr)\cdot\prod_{j=1,2}\prod_{i=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12-\nu_i-\mu_j+[a_i+c]\bigr)$.
--
--   This is the explicit archimedean evaluation of the dual (block-harmonic, or major) section of a real torus-triple integral: the integral, after multiplication by a single $\Gamma_{\mathbb R}$-factor, is a product of six $\Gamma_{\mathbb R}$-factors matching the expected $\mathrm{GL}_2\times\mathrm{GL}_2\times\mathrm{GL}_2$-type archimedean $L$-factor at the dual parameters, with constant $(-1)^c\rho$. It feeds the torus-pair identity used in the archimedean input to the converse theorem in the Langlands–Tunnell argument, and relies on the integrability statement for the same integrand and on the Gaussian-convolution $\Gamma_{\mathbb R}$-product formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR.lean

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

theorem LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR
    (ν₁ ν₂ : ℂ) (a₁ a₂ c : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (ha₀ : a₀ = c) (hsP : sP = a₁ + a₂) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + 1 + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ c.val * ρ * ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (a₁ + c))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (a₂ + c)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₁) + signShift (a₁ + c))) *
            Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₁) + signShift (a₂ + c)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₂) + signShift (a₁ + c))) *
              Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₂) + signShift (a₂ + c)))))) := by sorry
