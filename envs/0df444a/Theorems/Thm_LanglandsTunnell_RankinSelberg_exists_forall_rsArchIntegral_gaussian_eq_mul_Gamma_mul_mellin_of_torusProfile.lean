-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/7b1e9e79-e903-5b8c-8aeb-2a5393916197
-- title:
--   Archimedean Rankin–Selberg integral against the Gaussian for torus profiles
-- statement:
--   Work with $\mathrm{GL}_2(\mathbb R)$ carrying its Borel $\sigma$-algebra, and let [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) be the pullback of Lebesgue measure on $2\times 2$ real matrices weighted by $|\det g|^{-2}$. Assume this measure is a Haar measure, and fix a Haar measure $\mu_N$ on `realUnipotent`, the image of the homomorphism $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$. The assertion: there is a constant $C'>0$, independent of all data below, such that for all measurable $W,W':\mathrm{GL}_2(\mathbb R)\to\mathbb C$, every measurable $P:\mathbb R\to\mathbb R$ and every $x_0\in\mathbb R$ subject to: $W W'$ is left invariant under `realUnipotent` and right invariant under those $\kappa$ in `rowIsometrySubgroup ℝ` (the subgroup of $k$ with $\|\det k\|=1$ acting isometrically on row vectors) with $\det\kappa=1$; $(WW')(\mathrm{diag}(a_1,a_2))=P(a_1/a_2)$ for $a_1\neq0$, $a_2>0$; $P\ge 0$; $P$ is not almost everywhere $0$; and $y\mapsto P(y)|y|^{\sigma-2}$ is integrable for every real $\sigma>x_0$ — there exists $M:\mathbb C\to\mathbb C$, analytic on a neighbourhood of each point of $\{\operatorname{Re}s>x_0\}$, with $M(\sigma)$ real and of positive real part for real $\sigma>x_0$, given there by $M(s)=\int_{\mathbb R}P(y)|y|^{s-2}\,dy$, and such that for every $s$ with $\operatorname{Re}s>0$ for which $g\mapsto W(g)W'(g)e^{-\pi(g_{10}^2+g_{11}^2)}|\det g|^{s+1/2-1/2}$ is integrable against [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) weighted by [`HaarQuotient.density realUnipotent μN`](def/HaarQuotient.html#L25), the integral `rsArchIntegral` at parameter $s+\tfrac12$ of $W$ against $g\mapsto W'(g)e^{-\pi(g_{10}^2+g_{11}^2)}$ equals $C'\cdot\bigl(\tfrac12\pi^{-s}\Gamma(s)\bigr)\cdot M(s)$.
--
--   This is the archimedean separation step in the Rankin–Selberg computation: in Iwasawa coordinates the real local integral of a Whittaker-type product against the standard Gaussian on the bottom row splits as a Tate local zeta factor $\tfrac12\pi^{-s}\Gamma(s)$ times the Mellin transform of the profile $P$ describing the product on the diagonal torus. It feeds the global Rankin–Selberg package over $\mathbb Q$ for Godement–Eisenstein series, where analyticity and positivity of $M$ on the real ray are what is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile
    :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure)
      (μN : Measure realUnipotent) [μN.IsHaarMeasure],
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (W W' : GL (Fin 2) ℝ → ℂ) (P : ℝ → ℝ) (x₀ : ℝ)
        (_hW : Measurable W) (_hW' : Measurable W') (_hP : Measurable P)
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * W' (n * g) = W g * W' g)
        (_hK : ∀ κ ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * κ) * W' (g * κ) = W g * W' g)
        (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
          W (upperUnit a₁ 0 a₂ h₁ h₂.ne') * W' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ))
        (_hP0 : ∀ y : ℝ, 0 ≤ P y)
        (_hPne : ¬ (∀ᵐ y : ℝ, P y = 0))
        (_hPint : ∀ σ : ℝ, x₀ < σ → Integrable (fun y : ℝ => P y * |y| ^ (σ - 2))),
      ∃ M : ℂ → ℂ,
        AnalyticOnNhd ℂ M {s : ℂ | x₀ < s.re} ∧
        (∀ σ : ℝ, x₀ < σ → (M σ).im = 0 ∧ 0 < (M σ).re) ∧
        (∀ s : ℂ, x₀ < s.re → M s = ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) ∧
        ∀ s : ℂ, 0 < s.re →
          Integrable
            (fun g : GL (Fin 2) ℝ =>
              (W g * (W' g * Complex.exp (-(Real.pi *
                  (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
                (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
            (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN)) →
          rsArchIntegral RSCarrier.archMeasure μN (s + 1 / 2) W
              (fun g : GL (Fin 2) ℝ => W' g * Complex.exp (-(Real.pi *
                  (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) =
            (C' : ℂ) * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s) * M s := by sorry
