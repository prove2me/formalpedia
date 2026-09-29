-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/778373e3-612a-51bf-9a5c-3d5fe69c5a40
-- title:
--   Archimedean Rankin–Selberg integral of a discrete-series torus profile
-- statement:
--   Work with the Borel $\sigma$-algebra on $\mathrm{GL}_2(\mathbb{R})$, and let [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) be the pullback of Lebesgue measure on $2\times 2$ real matrices twisted by the density $|\det g|^{-2}$. Assume that this measure is a Haar measure, and let $\mu_N$ be a Haar measure on `realUnipotent`, the image of the homomorphism $\mathrm{Multiplicative}(\mathbb{R})\to\mathrm{GL}_2(\mathbb{R})$ sending $x$ to the upper unipotent matrix with entry $x$. Then there is a real $C'>0$ such that the following holds for every natural $k\ge 1$, every $C\in\mathbb{C}$ and all measurable $W,W'\colon\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ subject to: the product $WW'$ is left invariant under `realUnipotent`; $WW'$ is right invariant under those $\kappa$ in `rowIsometrySubgroup ℝ` (the subgroup of $\kappa$ with $\|\det \kappa\|=1$ for which $(x,y)\mapsto (x\kappa_{00}+y\kappa_{10},\,x\kappa_{01}+y\kappa_{11})$ preserves $\|x\|^2+\|y\|^2$) that satisfy $\det\kappa=1$; and, for $a_1\neq 0$ and $a_2>0$, the torus profile $(WW')(\mathrm{diag}(a_1,a_2))=C\,(a_1/a_2)^k e^{-4\pi a_1/a_2}$ when $a_1>0$ and $0$ otherwise, the diagonal matrix being `upperUnit a₁ 0 a₂`. Let $\sigma_0\ge 0$ and assume that for every $s$ with $\operatorname{Re} s>\sigma_0$ the function $g\mapsto W(g)\,W'(g)\,e^{-\pi(g_{10}^2+g_{11}^2)}\,|\det g|^{s+1/2-1/2}$ is integrable against [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) weighted by the density [`HaarQuotient.density realUnipotent μN`](def/HaarQuotient.html#L25) (namely `weight realUnipotent μN g` divided by its $\mu_N$-integral over the subgroup translates). Then for every such $s$, the integral `rsArchIntegral` of $W$ against $g\mapsto W'(g)e^{-\pi(g_{10}^2+g_{11}^2)}$ at parameter $s+\tfrac12$, i.e. the integral of $(WW'\cdot\text{Gaussian})(g)\,|\det g|^{(s+1/2)-1/2}$ for that weighted measure, equals $C'\,C\,(4\pi)^{-(s+k-1)}\Gamma(s+k-1)\cdot\pi^{-s}\Gamma(s)$.
--
--   This is the archimedean local Rankin–Selberg computation for the lowest weight vector of a holomorphic discrete series of weight $k$ paired with its partner and the standard Gaussian Godement section: the answer is $\Gamma_{\mathbb C}(s+k-1)\Gamma_{\mathbb R}(2s)$ up to a positive constant depending only on the chosen Haar measures. It supplies the infinite place in the global Rankin–Selberg identity [`AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat`](thm.html#AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat), and its proof reduces the carrier to an integral over the diagonal torus via [`LanglandsTunnell.Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal`](thm.html#LanglandsTunnell.Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.RankinSelberg.exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure)
      (μN : Measure realUnipotent) [μN.IsHaarMeasure],
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (k : ℕ) (_hk : 1 ≤ k) (C : ℂ) (W W' : GL (Fin 2) ℝ → ℂ)
        (_hW : Measurable W) (_hW' : Measurable W')
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * W' (n * g) = W g * W' g)
        (_hK : ∀ κ ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * κ) * W' (g * κ) = W g * W' g)
        (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
          W (upperUnit a₁ 0 a₂ h₁ h₂.ne') * W' (upperUnit a₁ 0 a₂ h₁ h₂.ne') =
            if 0 < a₁ then C * (((a₁ / a₂ : ℝ) : ℂ) ^ k * Complex.exp (-(4 * Real.pi * (a₁ / a₂) : ℝ))) else 0)
        (σ₀ : ℝ) (_hσ₀ : 0 ≤ σ₀)
        (_hint : ∀ s : ℂ, σ₀ < s.re → Integrable
          (fun g : GL (Fin 2) ℝ =>
            (W g * (W' g * Complex.exp (-(Real.pi *
                (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
              (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN))),
      ∀ s : ℂ, σ₀ < s.re →
        rsArchIntegral RSCarrier.archMeasure μN (s + 1 / 2) W
            (fun g : GL (Fin 2) ℝ => W' g * Complex.exp (-(Real.pi *
                (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) =
          (C' : ℂ) * C * ((4 * (Real.pi : ℂ)) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
            ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) := by sorry
