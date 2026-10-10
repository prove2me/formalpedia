-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_harmonic_real_analytic
-- name    : HunterPDE.Harmonic.harmonic_real_analytic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:08:06.364419+00:00
-- url     : https://prove2.me/theorems/87676516-39b7-454a-92b9-140974ce2972
-- title:
--   Theorem 2.10 — harmonic functions are real-analytic
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open. If $u \in C^2(\Omega)$ is harmonic in $\Omega$, then $u$ is **real-analytic** in $\Omega$: every $x \in \Omega$ has a neighbourhood on which $u$ is the sum of a convergent power series centred at $x$,
--   $$u(x + h) = \sum_{\alpha \in \mathbb{N}_0^n} \frac{\partial^\alpha u(x)}{\alpha!} h^\alpha \qquad (|h| \text{ small}).$$
--
--   A $C^2$ solution of Laplace's equation is therefore determined on a connected open set by its germ at a single point (Corollary 2.11); this is the prototype of analytic regularity for elliptic equations.
--
--   **Formalization Note.** Real-analytic in $\Omega$ is Mathlib's `AnalyticOnNhd ℝ u Ω` (analytic at every point of $\Omega$, i.e. a power series with positive radius converging to $u$ near each point); it is not analyticity on a single ball. Harmonic on the open set $\Omega$ is `InnerProductSpace.HarmonicOnNhd u Ω`. The statement holds for every $n$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 24, Theorem 2.10

import Mathlib

namespace HunterPDE.Harmonic

/-- Theorem 2.10 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 24: if `u ∈ C²(Ω)` is harmonic
in an open set `Ω ⊆ ℝⁿ`, then `u` is real-analytic in `Ω`: at every point of `Ω` it has a power
series expansion converging to `u` on a ball of positive radius (`AnalyticOnNhd ℝ u Ω`). -/
theorem harmonic_real_analytic {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω) :
    AnalyticOnNhd ℝ u Ω := by sorry

end HunterPDE.Harmonic
