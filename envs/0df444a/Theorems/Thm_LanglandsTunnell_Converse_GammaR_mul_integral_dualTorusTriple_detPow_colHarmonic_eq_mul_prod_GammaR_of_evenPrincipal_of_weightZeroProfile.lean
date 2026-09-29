-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_weightZeroProfile
-- name    : LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_weightZeroProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/b8f6f97e-76b7-5cab-bb3e-719772e5a4b1
-- title:
--   Γ-evaluation of the dual torus triple, even weight-zero case
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$, a class $b\in\mathbb Z/2$, and $W:\mathbb R\to\mathbb C$ continuous on $\{t\neq 0\}$ with $W(-t)=(-1)^{b}W(t)$ and satisfying, for $t>0$, the one-sheet Gaussian-convolution identity $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_0^\infty r^{\nu_1+\mathrm{signShift}(b+b)}e^{-\pi r^2}(t/r)^{\nu_2+\mathrm{signShift}(b+b)}e^{-\pi(t/r)^2}\,dr/r$, where $\mathrm{signShift}(a)$ is $0$ for $a=0$ and $1$ otherwise. Fix $u_1,u_2\in\mathbb C$ and a real archimedean Whittaker datum $D$ of type $P_2$ (a smooth function on $2\times2$ real matrices with $\psi$-equivariance under unipotents, the central character law of $P_2$, entire zeta functions whose Mellin integrals equal the archimedean $\Gamma$-factor of the twisted parameter times an entire function of finite order obeying the functional equation, and the prescribed decay at $0$ and $\infty$), with $P_2=\mathrm{principal}(u_1,b,u_2,b)$, so $P_2$'s central exponent is $u_1+u_2$. Assume a weight-zero torus profile: for $\tau>0$, $D.W(\mathrm{diag}(\tau,1))=\rho\,\tau\cdot 4\int_0^\infty r^{u_1}e^{-\pi r^2}(\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\,dr/r$, together with $D.W(\mathrm{diag}(-\tau,1))=(-1)^{b}D.W(\mathrm{diag}(\tau,1))$ for $\tau>0$. Finally let $a=-1$, $u_0\in\mathbb C$, $c_P=\nu_1+\nu_2$, $a_0\in\mathbb Z/2$, $s_P=b+b$, $n=0$, and $\delta\in\{0,1\}$ with $\delta\equiv a_0+b \pmod 2$. The assertion is that there is $\sigma\in\mathbb R$ such that for all $s$ with $\operatorname{Re}s>\sigma$, the product of $\Gamma_{\mathbb R}(2s-c_P-(u_1+u_2)+n+1)$ with the triple integral over $t\in\mathbb R$, $q\in\mathbb R$, $p\in(0,\infty)$ of the kernel formed from the sign characters $\mathrm{quasiChar}\,0\,s_P(-t)\,\mathrm{quasiChar}\,0\,a_0(-t)\,\mathrm{quasiChar}\,0\,1\,t\,\mathrm{quasiChar}\,0\,(n\bmod 2)\,q\,\mathrm{quasiChar}\,0\,a_0\,q$ (here $\mathrm{quasiChar}\,u\,a\,y=|y|^{u}$ times $\mathrm{sign}(y)$ when $a\neq0$), the factor $W(-t)\bigl((p\,\mathrm{quasiChar}\,0\,1\,t)(a^2\,\mathrm{quasiChar}\,0\,1\,t\,(pq)^{-1})^{\delta}\bigr)D.W(\mathrm{diag}(a|t|p/q,1))$, the power factor $|t|^{s-5/2-c_P-(u_1+u_2)}|q|^{u_0+c_P+(u_1+u_2)-2s-1}p^{u_0-(u_1+u_2)-3}$ and the Gaussians $e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$, equals $(-1)^{b+\delta}\rho$ times the six-fold product $\prod_{i=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12+(-\nu_i-u_0)+\mathrm{signShift}(b+a_0)\bigr)\cdot\prod_{i,j=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12+(-\nu_i-u_j)+\mathrm{signShift}(b+b)\bigr)$.
--
--   This is the archimedean $\Gamma$-factor evaluation of the dual torus triple attached to the even-type section built from a determinant power and a column harmonic of degree $n=0$, in the case where the second parameter is principal with weight-zero torus profile: the triple integral collapses, up to the explicit constant $(-1)^{b+\delta}\rho$ and one inverse $\Gamma_{\mathbb R}$, to the six $\Gamma_{\mathbb R}$-factors of a $\mathrm{GL}_2\times\mathrm{GL}_2$ Rankin–Selberg Euler factor at infinity. It feeds the identification of the dual torus pair with the archimedean root number times the expected $\Gamma$-factor, a step in the converse-theorem input to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_weightZeroProfile.lean

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

theorem LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_weightZeroProfile
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u₁ u₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal u₁ b u₂ b)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = b + b)
    (n : ℕ) (hn : n = 0) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (b.val + δ) * ρ *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (b + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (b + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₁) + signShift (b + b))) *
            Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₁) + signShift (b + b)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₂) + signShift (b + b))) *
              Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₂) + signShift (b + b)))))) := by sorry
