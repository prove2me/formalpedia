-- Prove2me | Theorems.Thm_MasulloRH_sobolev_spectral_synthesis
-- name    : MasulloRH.sobolev_spectral_synthesis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:12:39.013543+00:00
-- url     : https://prove2.me/theorems/50593736-7c02-4197-a08c-bf9fbd74d127
-- title:
--   The weighted Hilbert annihilator of an analytic multiplier is the closed span of its admissible jets
-- statement:
--   Let $p>1/2$, $w_p(x)=(1+x^2)^{-p/2}$, and let $G:\mathbb R\to\mathbb C$ be real analytic with finite order of vanishing at every point. Given $u\in L^2(\mathbb R)$, pair it with a frequency test $f$ by $D_u(f)=\int_{\mathbb R} w_p(x)^{-1}u(x)\,\mathcal F^{-1}f(x)\,dx$.
--
--   Then $D_u(Gq)=0$ for every smooth compactly supported $q$ if and only if $u$ belongs to the $L^2$-closed linear span of
--   $$
--   w_p(x)x^r e^{-2\pi i x\nu},\qquad G(\nu)=0,\quad 0\le r<\operatorname{ord}_\nu G,\quad r+\tfrac12<p.
--   $$
--   The strict final inequality gives the exact jet cutoff, including half-integer values of $p$. The zero set may be infinite and need not be uniformly separated.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, pp. 65–68, especially (27)–(38), https://arxiv.org/abs/math/9811068. Real-line Hilbert-space spectral synthesis for the fixed-line construction in A. M. Masullo, The Music of the Primes, §10.2.1.1. The unit-band repair was proposed by Calvin Yost-Wolff in Prove2Me discussion d8680fb7-dd35-4a9c-ab4e-5888ec240d48.

import Mathlib
open MeasureTheory
open scoped SchwartzMap FourierTransform Topology

theorem MasulloRH.sobolev_spectral_synthesis (p : ℝ) (hp : 1/2<p) (G : ℝ→ℂ)
    (hG : ∀ x, AnalyticAt ℝ G x) (hfin : ∀ x, analyticOrderAt G x ≠ ⊤)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∀ q : 𝓢(ℝ,ℂ), HasCompactSupport (q:ℝ→ℂ) →
      ∫ x : ℝ, (↑((1+x^2)^(p/2) : ℝ) * (𝓕⁻ (fun t : ℝ => G t * q t)) x : ℂ) * u x = 0) ↔
    u ∈ (Submodule.span ℂ {v : Lp ℂ 2 (volume : Measure ℝ) | ∃ (ν : ℝ) (r : ℕ),
      G ν = 0 ∧ r < analyticOrderNatAt G ν ∧ (r:ℝ)+1/2<p ∧
      (v : ℝ→ℂ) =ᵐ[volume] (fun x : ℝ => (↑((1+x^2)^(-p/2) : ℝ) : ℂ) *
        ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν)*Complex.I)))}).topologicalClosure := by sorry
