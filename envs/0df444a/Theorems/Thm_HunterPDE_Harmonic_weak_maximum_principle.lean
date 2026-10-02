-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_weak_maximum_principle
-- name    : HunterPDE.Harmonic.weak_maximum_principle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:09:54.977043+00:00
-- url     : https://prove2.me/theorems/7f9f4d3e-3d85-411d-8409-1009586a7e66
-- title:
--   Theorem 2.17 — weak maximum principle on a bounded connected domain
-- statement:
--   Let $n \ge 1$ and let $\Omega \subseteq \mathbb{R}^n$ be a bounded, connected open set. If $u \in C^2(\Omega) \cap C(\overline{\Omega})$ is harmonic in $\Omega$, then
--   $$\max_{\overline{\Omega}} u = \max_{\partial\Omega} u, \qquad \min_{\overline{\Omega}} u = \min_{\partial\Omega} u.$$
--
--   A harmonic function on a bounded domain is thus controlled by its boundary values, which gives uniqueness for the Dirichlet problem (Theorem 2.18).
--
--   **Formalization Note.** $\overline{\Omega}$ is `closure Ω` and $\partial\Omega$ is `frontier Ω`. Each equality is stated as attainment: some point $y \in \partial\Omega$ satisfies $u(z) \le u(y)$ for all $z \in \overline{\Omega}$ (respectively $u(y) \le u(z)$). Both maxima exist by compactness, and since $\partial\Omega \subseteq \overline{\Omega}$ this is equivalent to the equality of maxima. Connected is `IsConnected Ω` (which includes nonempty). The hypothesis $n \ge 1$ is the book's ambient dimension: for $n = 0$ the whole one-point space is a bounded connected open set with empty boundary.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 27, Theorem 2.17

import Mathlib

namespace HunterPDE.Harmonic

/-- Theorem 2.17 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 27 (weak maximum principle):
if `Ω ⊆ ℝⁿ` is a bounded, connected open set and `u ∈ C²(Ω) ∩ C(Ω̄)` is harmonic in `Ω`, then
`max_{Ω̄} u = max_{∂Ω} u` and `min_{Ω̄} u = min_{∂Ω} u`. Each equality is stated as: some point of
`∂Ω = frontier Ω` is a maximum (resp. minimum) point of `u` on `Ω̄ = closure Ω`. Connected includes
nonempty (`IsConnected`), and `n ≥ 1` (for `n = 0` the only nonempty open set is the whole
one-point space, whose boundary is empty). -/
theorem weak_maximum_principle {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (hconn : IsConnected Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    (hcont : ContinuousOn u (closure Ω)) :
    (∃ y ∈ frontier Ω, ∀ x ∈ closure Ω, u x ≤ u y) ∧
      (∃ y ∈ frontier Ω, ∀ x ∈ closure Ω, u y ≤ u x) := by sorry

end HunterPDE.Harmonic
