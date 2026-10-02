-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_dirichlet_existence
-- name    : HunterPDE.Elliptic.dirichlet_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:46:49.102669+00:00
-- url     : https://prove2.me/theorems/5e4c9c6f-e411-4f38-843d-3901a1e28e5a
-- title:
--   Theorem 4.11 — unique weak solution of −Δu = f in H¹₀(Ω) for f ∈ H⁻¹(Ω)
-- statement:
--   Let $\Omega$ be an open set in $\mathbb{R}^n$ that is bounded in some direction, and let $f \in H^{-1}(\Omega)$ be a bounded linear functional on $H^1_0(\Omega)$. Then there is a unique weak solution $u \in H^1_0(\Omega)$ of $-\Delta u = f$ in the sense of Definition 4.2, that is,
--   $$\int_\Omega Du\cdot D\phi\,dx = \langle f, \phi\rangle \qquad \text{for all } \phi \in H^1_0(\Omega).$$
--
--   This is the model existence theorem of the chapter: the weak Dirichlet problem for the Laplacian is well posed.
--
--   **Formalization Note.** $H^{-1}(\Omega)$ is `StrongDual ℝ (H10 n Ω)`, the bounded linear functionals on $H^1_0(\Omega)$ with its standard norm (Definition 4.1).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 99, Theorem 4.11

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_H10

open MeasureTheory

namespace HunterPDE.Elliptic

/-- Theorem 4.11 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 99: if `Ω` is an open set in
`ℝⁿ` that is bounded in some direction and `f ∈ H⁻¹(Ω)`, then there is a unique weak solution
`u ∈ H¹₀(Ω)` of `−Δu = f` in the sense of Definition 4.2, i.e.
`∫_Ω Du · Dφ dx = ⟨f, φ⟩` for all `φ ∈ H¹₀(Ω)`.
`H⁻¹(Ω)` is the space of bounded linear functionals on `H¹₀(Ω)` with its standard norm
(Definition 4.1), `StrongDual ℝ (H10 n Ω)`. -/
theorem dirichlet_existence {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩd : BoundedInSomeDirection Ω) (f : StrongDual ℝ (H10 n Ω)) :
    ∃! u : H10 n Ω, ∀ φ : H10 n Ω, ∫ x in Ω, inner ℝ (grad u x) (grad φ x) = f φ := by sorry

end HunterPDE.Elliptic
