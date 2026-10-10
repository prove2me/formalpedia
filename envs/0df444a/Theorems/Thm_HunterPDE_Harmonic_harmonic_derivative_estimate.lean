-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_harmonic_derivative_estimate
-- name    : HunterPDE.Harmonic.harmonic_derivative_estimate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:04:54.676983+00:00
-- url     : https://prove2.me/theorems/a79740c7-c0bd-44f5-8908-203ffa562cd4
-- title:
--   Theorem 2.7 — first-derivative estimate |∂ᵢu(x)| ≤ (n/r) max |u| for harmonic u
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open, let $u \in C^2(\Omega)$ be harmonic in $\Omega$, and let $B_r(x) \Subset \Omega$. Then for every $1 \le i \le n$
--   $$|\partial_i u(x)| \le \frac{n}{r} \max_{\overline{B}_r(x)} |u|.$$
--
--   The estimate bounds a derivative of a harmonic function at a point by the size of the function on a surrounding ball; it gives Liouville's theorem (Corollary 2.8) and is the base case of the higher-order estimate (Theorem 2.9).
--
--   **Formalization Note.** The maximum over the closed ball is expressed through an arbitrary bound: for every real $M$ with $|u| \le M$ on $\overline{B}_r(x)$, $|\partial_i u(x)| \le (n/r) M$. Since $u$ is continuous on the compact ball the maximum is attained, so taking $M = \max_{\overline{B}_r(x)} |u|$ recovers the book's form, and the two are equivalent. Coordinates are 0-based (`i : Fin n`); $\partial_i u$ is `HunterPDE.Shared.partialDeriv u i` from the shared definition `HunterPDE.Shared.PartialDeriv`. Harmonic on $\Omega$ is `InnerProductSpace.HarmonicOnNhd u Ω`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 23, Theorem 2.7

import Mathlib
import Definitions.Def_HunterPDE_Shared_PartialDeriv

namespace HunterPDE.Harmonic

/-- Theorem 2.7 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 23: if `u ∈ C²(Ω)` is harmonic
in the open set `Ω ⊆ ℝⁿ` and `B_r(x) ⋐ Ω`, then for every coordinate `i`,
`|∂ᵢu(x)| ≤ (n / r) max_{B̄_r(x)} |u|`. The maximum is expressed through an arbitrary bound `M`
of `|u|` on the closed ball `B̄_r(x)` (taking `M` to be the maximum gives the book's form). -/
theorem harmonic_derivative_estimate {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Ω)
    (i : Fin n) {M : ℝ} (hM : ∀ y ∈ Metric.closedBall x r, |u y| ≤ M) :
    |Shared.partialDeriv u i x| ≤ (n / r) * M := by sorry

end HunterPDE.Harmonic
