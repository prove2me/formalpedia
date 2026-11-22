-- Prove2me | Theorems.Thm_HardyDisc_ae_exists_tendsto_nontangential
-- name    : HardyDisc.ae_exists_tendsto_nontangential
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:25:53.961795+00:00
-- url     : https://prove2.me/theorems/32ba9e29-7176-4aab-b58b-b5a9c9a3cc6d
-- title:
--   Every $F\in H^p(\mathbb D)$, $0<p\le\infty$, has nontangential boundary limits at almost every point of the unit circle
-- statement:
--   **Fatou–Riesz theorem for the Hardy spaces of the unit disc: nontangential boundary limits.** Let $0<p\le\infty$ and let $F\in H^p(\mathbb D)$: the function $F$ is holomorphic on the open unit disc $\mathbb D=\{w\in\mathbb C:|w|<1\}$ and its integral means on the circles $|w|=r$ are bounded,
--
--   $$\sup_{0<r<1}\Bigl(\int_0^{2\pi}|F(re^{i\theta})|^p\,\mathrm d\theta\Bigr)^{1/p}<\infty$$
--
--   (for $p=\infty$: $\sup_{0<r<1}\operatorname{ess\,sup}_\theta|F(re^{i\theta})|<\infty$, i.e. $F$ is bounded). For $\theta\in\mathbb R$ and $M>0$ let
--
--   $$\Gamma_M(\theta)=\{w\in\mathbb D:\ |e^{i\theta}-w|\le M\,(1-|w|)\}$$
--
--   be the Stolz region of aperture $M$ with vertex $e^{i\theta}$. Then $F$ has a nontangential limit at almost every point of the unit circle: for Lebesgue-almost every $\theta\in\mathbb R$ there is $L\in\mathbb C$ such that, for every $M$,
--
--   $$\lim_{\substack{w\to e^{i\theta}\\ w\in\Gamma_M(\theta)}}F(w)=L .$$
--
--   This is the classical boundary-value theorem for $H^p$ of the disc (Fatou for bounded functions, F. Riesz for $0<p<\infty$). It is the disc counterpart of the existence of the boundary function $f_\Phi=\lim_{\sigma\to a^-}\Phi(\sigma+iy)$ of a Hardy function $\Phi$ on a half-plane, which the source recalls in §B.2.1; the half-plane statement follows from it after transplanting $\Phi$ to the disc by a Möbius map, since horizontal rays ending on the boundary line are carried into Stolz regions.
--
--   **Formalization Note.** The exponent is `p : ℝ≥0∞` with `p ≠ 0`; the case `p = ⊤` (bounded holomorphic functions) is included. The integral means are Mathlib's `eLpNorm` of `θ ↦ F (circleMap 0 r θ)` with respect to Lebesgue measure on $(0,2\pi]$, bounded by a finite constant `C : ℝ≥0∞`. "Almost every $\theta$" refers to Lebesgue measure on $\mathbb R$ (the parametrisation $\theta\mapsto e^{i\theta}$ is periodic). The nontangential limit is `Tendsto F (𝓝[Γ_M(θ)] e^{iθ}) (𝓝 L)`, required for every real `M` with one and the same `L`; for `M < 1` the region is empty and the condition is vacuous.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 592, §B.2.1 (existence almost everywhere and $L^p$-membership of the boundary function $f_\Phi$, recalled from [Dur, Cor. to Thm. 11.1]); auxiliary lemma for the proof of HardyHalfPlane.exists_boundary_function; classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Chapter 2 (Basic structure of $H^p$ functions: nontangential limits almost everywhere)

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace HardyDisc

theorem ae_exists_tendsto_nontangential (F : ℂ → ℂ) (p : ℝ≥0∞) (hp0 : p ≠ 0)
    (hF : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1))
    (hbound : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ r : ℝ, 0 < r → r < 1 →
      eLpNorm (fun θ : ℝ => F (circleMap 0 r θ)) p
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) ≤ C) :
    ∀ᵐ θ : ℝ ∂volume, ∃ L : ℂ, ∀ M : ℝ,
      Tendsto F
        (𝓝[{w : ℂ | ‖w‖ < 1 ∧ ‖circleMap 0 1 θ - w‖ ≤ M * (1 - ‖w‖)}] (circleMap 0 1 θ))
        (𝓝 L) := by sorry

end HardyDisc
