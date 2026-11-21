-- Prove2me | Theorems.Thm_MasulloRH_rational_theta_test_factorization
-- name    : MasulloRH.rational_theta_test_factorization
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:13:14.154115+00:00
-- url     : https://prove2.me/theorems/5398f12a-67e4-4347-a222-981564f719c1
-- title:
--   Rational theta tests have Schwartz logarithmic profiles and vanish to the full zeta order
-- statement:
--   For every complex Schwartz function $g$ on $\mathbb R$ satisfying $g(0)=\int_{\mathbb R}g=0$, set $\theta_g(a)=\sum_{n\in\mathbb Z}g(na)$ for $a>0$. The profile $T_g(x)=e^{x/2}\theta_g(e^x)$ is Schwartz. Its Fourier transform at $\nu$ equals $\mathcal M\theta_g(1/2-2\pi i\nu)$. Throughout $\Re s>0$, $s\ne1$, the Mellin integral converges and satisfies
--   $$
--   \mathcal M\theta_g(s)=\zeta(s)\int_0^\infty [g(a)+g(-a)]a^{s-1}\,da .
--   $$
--   Its vanishing order at every such $s$ is at least the order of $\zeta$. In particular all real frequency derivatives of $\widehat T_g$ of order below $\operatorname{ord}_{1/2-2\pi i\nu}\zeta$ vanish at $\nu$.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, (14)–(26), https://arxiv.org/abs/math/9811068. Rational real-place calculation for A. M. Masullo, The Music of the Primes, §10.2.1.1. Companion to the exact-order dyadic Gaussian generator, Prove2Me theorem 714a2f7b-e260-4499-9c88-2074add3de2b.

import Mathlib
open Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform

theorem MasulloRH.rational_theta_test_factorization (g : 𝓢(ℝ,ℂ)) (hg : g 0 = 0) (hI : (∫ t : ℝ, g t) = 0) :
    let θ := fun a : ℝ => ∑' n : ℤ, g ((n:ℝ)*a)
    let σ := fun ν : ℝ => (1/2:ℂ) + ((-2*Real.pi:ℝ):ℂ)*Complex.I*(ν:ℂ)
    (∀ s : ℂ, 0 < s.re → s ≠ 1 →
      HasMellin θ s (riemannZeta s * mellin (fun a : ℝ => g a + g (-a)) s) ∧
      analyticOrderAt riemannZeta s ≤ analyticOrderAt (mellin θ) s) ∧
    ∃ T : 𝓢(ℝ,ℂ), (∀ x : ℝ, T x = (Real.exp (x/2):ℂ) * θ (Real.exp x)) ∧
      (∀ ν : ℝ, (𝓕 T) ν = mellin θ (σ ν)) ∧
      ∀ ν : ℝ, AnalyticAt ℝ (fun x : ℝ => (𝓕 T : 𝓢(ℝ,ℂ)) x) ν ∧
        analyticOrderAt riemannZeta (σ ν) ≤ analyticOrderAt (fun x : ℝ => (𝓕 T : 𝓢(ℝ,ℂ)) x) ν ∧
        ∀ j < analyticOrderNatAt riemannZeta (σ ν),
          iteratedDeriv j (fun x : ℝ => (𝓕 T : 𝓢(ℝ,ℂ)) x) ν = 0 := by sorry
