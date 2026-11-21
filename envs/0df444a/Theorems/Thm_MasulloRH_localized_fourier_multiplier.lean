-- Prove2me | Theorems.Thm_MasulloRH_localized_fourier_multiplier
-- name    : MasulloRH.localized_fourier_multiplier
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:36:42.445906+00:00
-- url     : https://prove2.me/theorems/8233cb07-83fb-4d3b-8b25-d83f36c6f103
-- title:
--   Rapid decay of the weighted integrals of inverse Fourier band kernels
-- statement:
--   Let $m$ and $\theta$ be complex Schwartz functions on $\mathbb R$. For $j\in\mathbb R$, let $K_j$ be the inverse Fourier transform of the function $\xi\mapsto m(\xi)\theta(\xi-j)$. For all nonnegative integers $k,N$ there is a constant $C\ge 0$ such that $(1+|x|)^k|K_j(x)|$ is integrable for every $j$ and
--   $$
--   (1+|j|)^N\int_{\mathbb R}(1+|x|)^k|K_j(x)|\,dx\le C.
--   $$
--   This controls the integrated action of each frequency band on a representation with polynomially growing translation norms. It supplies the quantitative decay in the critical-line spectral trace argument.
-- source:
--   Analytic estimate for the frequency localization in A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, preprint pp. 67–68, equations (35)–(36), https://arxiv.org/abs/math/9811068. Related to A. M. Masullo, The Music of the Primes, §10.3.1, pp. 447–451. The application to Masullo §10.3.1 follows the smooth-window proposal by Calvin Yost-Wolff in the Prove2Me mission discussion, 20 November 2026, 22:19 UTC (comment d8680fb7-dd35-4a9c-ab4e-5888ec240d48).

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
open scoped SchwartzMap FourierTransform
open MeasureTheory

theorem MasulloRH.localized_fourier_multiplier (m θ : 𝓢(ℝ, ℂ)) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℝ,
      Integrable (fun x : ℝ => (1+|x|)^k * ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-j))) x‖) ∧
      (1+|j|)^N * (∫ x : ℝ, (1+|x|)^k * ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-j))) x‖) ≤ C := by sorry
