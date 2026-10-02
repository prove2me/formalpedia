-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_strong_maximum_principle
-- name    : HunterPDE.Harmonic.strong_maximum_principle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:08:42.911067+00:00
-- url     : https://prove2.me/theorems/6c90159c-4613-4cb7-876f-da9292d31551
-- title:
--   Theorem 2.13 — strong maximum principle for subharmonic functions
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be a connected open set and $u \in C^2(\Omega)$. If $u$ is subharmonic ($\Delta u \ge 0$ in $\Omega$) and attains a global maximum value in $\Omega$, i.e. there is $x_0 \in \Omega$ with
--   $$u(x) \le u(x_0) \qquad \text{for all } x \in \Omega,$$
--   then $u$ is constant in $\Omega$.
--
--   Applied to $u$ and $-u$ it gives the strong maximum and minimum principle for harmonic functions (Theorem 2.15).
--
--   **Formalization Note.** Subharmonicity (with $u \in C^2(\Omega)$) is `IsSubharmonicOn Ω u` from the definition item `Subharmonic`. Connectedness is `IsPreconnected Ω`; nonemptiness is implied by the existence of the maximum point, so this is the book's "connected". Constant in $\Omega$ is $\exists c, \forall x \in \Omega, u(x) = c$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 26, Theorem 2.13

import Mathlib
import Definitions.Def_HunterPDE_Harmonic_Subharmonic

namespace HunterPDE.Harmonic

/-- Theorem 2.13 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 26 (strong maximum
principle): if `Ω ⊆ ℝⁿ` is a connected open set, `u ∈ C²(Ω)` is subharmonic (`Δu ≥ 0` in `Ω`) and
`u` attains a global maximum value in `Ω` (at some `x₀ ∈ Ω`), then `u` is constant in `Ω`. -/
theorem strong_maximum_principle {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hu : IsSubharmonicOn Ω u) (hmax : ∃ x₀ ∈ Ω, ∀ x ∈ Ω, u x ≤ u x₀) :
    ∃ c : ℝ, ∀ x ∈ Ω, u x = c := by sorry

end HunterPDE.Harmonic
