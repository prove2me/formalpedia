-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_smooth_of_mean_value_property
-- name    : HunterPDE.Harmonic.smooth_of_mean_value_property
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:03:01.498246+00:00
-- url     : https://prove2.me/theorems/d21e4fb9-80b5-4505-9a39-f0831b33961c
-- title:
--   Theorem 2.2 — a continuous function with the mean-value property is smooth and harmonic
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and let $u \in C(\Omega)$ have the mean-value property (2.3): for every ball $B_r(x) \Subset \Omega$,
--   $$u(x) = ⨍_{B_r(x)} u \, dx \quad\text{and}\quad u(x) = ⨍_{\partial B_r(x)} u \, dS.$$
--   Then $u \in C^\infty(\Omega)$ and $\Delta u = 0$ in $\Omega$.
--
--   Together with Theorem 2.1 this characterizes harmonic functions by the mean-value property and shows that every $C^2$ harmonic function is $C^\infty$, which the proof of analyticity (Theorem 2.10) uses.
--
--   **Formalization Note.** $u \in C(\Omega)$ is `ContinuousOn u Ω`; the mean-value property is `HasMeanValueProperty Ω u` from the definition item `MeanValue` (both identities of (2.3), for every $r > 0$ with $\overline{B}_r(x) \subseteq \Omega$). $C^\infty$ is `ContDiffOn ℝ ∞ u Ω` with `∞` the smooth order (not `ω`, which would be analyticity). $\Delta$ is Mathlib's `laplacian`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 21, Theorem 2.2

import Mathlib
import Definitions.Def_HunterPDE_Harmonic_MeanValue

open Laplacian
open scoped ContDiff

namespace HunterPDE.Harmonic

/-- Theorem 2.2 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 21: if `u ∈ C(Ω)` has the
mean-value property (2.3) in the open set `Ω ⊆ ℝⁿ`, then `u ∈ C^∞(Ω)` and `Δu = 0` in `Ω`.
`∞` is `C^∞` (not `ω`, which would be analyticity). -/
theorem smooth_of_mean_value_property {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hmv : HasMeanValueProperty Ω u) :
    ContDiffOn ℝ ∞ u Ω ∧ ∀ x ∈ Ω, Δ u x = 0 := by sorry

end HunterPDE.Harmonic
