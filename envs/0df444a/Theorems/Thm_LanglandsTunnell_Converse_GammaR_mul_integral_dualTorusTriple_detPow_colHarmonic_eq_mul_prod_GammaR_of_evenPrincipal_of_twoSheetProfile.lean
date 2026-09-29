-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_twoSheetProfile
-- name    : LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_twoSheetProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/28580407-4728-54fc-9ba6-de82946af99a
-- title:
--   Γ-evaluation of the dual torus triple, even principal two-sheet profile
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$ and $b\in\mathbb Z/2$, and let $W:\mathbb R\to\mathbb C$ be continuous on $\{t\neq 0\}$, of parity $W(-t)=(-1)^{b}W(t)$, and such that for $t>0$ the even combination $W(t)+(-1)^{b}W(-t)$ equals $t$ times the Gaussian convolution kernel $4\int_0^\infty r^{\nu_1+\mathrm{signShift}(b+b)}e^{-\pi r^2}(t/r)^{\nu_2+\mathrm{signShift}(b+b)}e^{-\pi(t/r)^2}\,dr/r$, where $\mathrm{signShift}(a)$ is $0$ for $a=0$ and $1$ otherwise (so $\mathrm{signShift}(b+b)=0$). Let $u_1,u_2\in\mathbb C$, $c_1\neq c_2$ in $\mathbb Z/2$, let $D$ be a real archimedean Whittaker datum `ArchDatumR` for $P_2$ (a Whittaker function on $2\times 2$ real matrices, smooth on the invertible locus, with unipotent and central transformation laws, entire zeta integrals obeying the functional equation, and the prescribed growth and decay bounds), with $P_2=\mathrm{principal}(u_1,c_1,u_2,c_2)$, and suppose $\rho\in\mathbb C$ is such that for every $b'\in\mathbb Z/2$ and $\tau>0$ one has $D.W(\mathrm{diag}(\tau,1))+(-1)^{b'}D.W(\mathrm{diag}(-\tau,1))=\rho\,\tau$ times the analogous kernel with exponents $u_1+\mathrm{signShift}(c_1+b')$ and $u_2+\mathrm{signShift}(c_2+b')$. Finally let $a=-1$, $u_0\in\mathbb C$, $c_P=\nu_1+\nu_2$, $a_0,s_P\in\mathbb Z/2$ with $s_P=b+b$, $n=1$, and $\delta\in\{0,1\}$ with $\delta\equiv a_0+b \pmod 2$. The assertion is that there exists $\sigma\in\mathbb R$ such that for all $s$ with $\mathrm{Re}\,s>\sigma$, the product of $\Gamma_{\mathbb R}(2s-c_P-c(P_2)+n+1)$, where $c(P_2)=u_1+u_2$ is the central exponent, with the triple integral over $t\in\mathbb R$, $q\in\mathbb R$, $p\in(0,\infty)$ of the displayed integrand — the product of the five sign characters $\mathrm{quasiChar}\,0\,\cdot$ in $-t$, $t$ and $q$, the factor $W(-t)\,\bigl(p\,\mathrm{sign}(t)\bigr)\bigl(a^2\,\mathrm{sign}(t)(pq)^{-1}\bigr)^{\delta}D.W(\mathrm{diag}(a|t|p/q,1))$, the powers $|t|^{s-5/2-c_P-c(P_2)}|q|^{u_0+c_P+c(P_2)-2s-1}p^{u_0-c(P_2)-3}$, and the Gaussians $e^{-\pi t^2p^2}e^{-\pi a^2/p^2}e^{-\pi a^2/q^2}$ — equals $(-1)^{b+\delta+1}\rho\cdot\tfrac12$ times the six-fold product $\prod_{i=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12-\nu_i-u_0+\mathrm{signShift}(b+a_0)\bigr)\prod_{i,j=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12-\nu_i-u_j+\mathrm{signShift}(b+c_j)\bigr)$.
--
--   This is the archimedean evaluation step in the Rankin–Selberg half of the converse-theorem input to Langlands–Tunnell: it identifies an explicit triple integral built from a Gaussian-type Whittaker sheet for $GL(2)$ and a principal-series archimedean Whittaker datum with a product of six $\Gamma_{\mathbb R}$-factors, i.e. with the expected $GL(2)\times GL(3)$ archimedean $L$-factor, on the even-type section of weight-one (two-sheet) Levi profile. It feeds the computation of the dual torus pair in `LanglandsTunnell.RankinSelberg`, and rests on the Barnes-type integral evaluation [`LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance`](thm.html#LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance) together with the integrability statement for the same kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_twoSheetProfile.lean

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

theorem LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_twoSheetProfile
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hc : c₁ ≠ c₂) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂)
    (ρ : ℂ)
    (hρ : ∀ (b' : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b'.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b')) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b')) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = b + b)
    (n : ℕ) (hn : n = 1) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (b.val + δ + 1) * ρ * (1 / 2 : ℂ) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (b + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (b + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₁) + signShift (b + c₁))) *
            Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₁) + signShift (b + c₁)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₂) + signShift (b + c₂))) *
              Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₂) + signShift (b + c₂)))))) := by sorry
