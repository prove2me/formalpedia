-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_mean_value_property
-- name    : HunterPDE.Harmonic.mean_value_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:01:51.494089+00:00
-- url     : https://prove2.me/theorems/d9b9b356-8b65-4965-bc2e-cbdd195e4a9b
-- title:
--   Theorem 2.1 — mean value property of harmonic functions on balls and spheres
-- statement:
--   Let $n \ge 1$, let $\Omega \subseteq \mathbb{R}^n$ be open and let $u \in C^2(\Omega)$ be harmonic in $\Omega$, i.e. $\Delta u = 0$ in $\Omega$. If $B_r(x) \Subset \Omega$ (with $r > 0$, the closed ball $\overline{B}_r(x)$ lies in $\Omega$), then $u(x)$ equals both its average over the ball and its average over the sphere:
--   $$u(x) = ⨍_{B_r(x)} u \, dx, \qquad u(x) = ⨍_{\partial B_r(x)} u \, dS. \qquad (2.3)$$
--
--   This is the basic tool of the chapter: the derivative estimates (Theorems 2.7, 2.9), analyticity (Theorem 2.10) and the maximum principle all rest on it.
--
--   **Formalization Note.** "Harmonic, $u \in C^2(\Omega)$" on the open set $\Omega$ is Mathlib's `InnerProductSpace.HarmonicOnNhd u Ω` ($C^2$ near every point of $\Omega$ and $\Delta u = 0$ near every point). $B_r(x) \Subset \Omega$ is `0 < r` and `Metric.closedBall x r ⊆ Ω`. The sphere average is `sphereAverage` from the definition item `MeanValue`. The hypothesis $n \ge 1$ makes the sphere nonempty (for $n = 0$ it is empty and its average is the junk value $0$); the book works in $\mathbb{R}^n$ with $n \ge 1$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 20, Theorem 2.1

import Mathlib
import Definitions.Def_HunterPDE_Harmonic_MeanValue

open MeasureTheory

namespace HunterPDE.Harmonic

/-- Theorem 2.1 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 20: if `u ∈ C²(Ω)` is harmonic
in an open set `Ω ⊆ ℝⁿ` and `B_r(x) ⋐ Ω` (the closed ball lies in `Ω`, `r > 0`), then `u(x)` is
the average of `u` over the ball `B_r(x)` and over the sphere `∂B_r(x)`. Harmonic on the open set
`Ω` is Mathlib's `HarmonicOnNhd` (`C²` near every point of `Ω` and `Δu = 0` there). -/
theorem mean_value_property {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Ω) :
    u x = (⨍ y in Metric.ball x r, u y) ∧ u x = sphereAverage u x r := by sorry

end HunterPDE.Harmonic
