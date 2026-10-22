-- Prove2me | Theorems.Thm_GeomDL_Blueprint_exists_representation_act
-- name    : GeomDL.Blueprint.exists_representation_act
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:21.691994+00:00
-- url     : https://prove2.me/theorems/da286570-1470-4255-95c7-785363799546
-- title:
--   §3.1, p. 15 — ρ(g)x(u) = x(g⁻¹u) is a linear representation: ρ(g)(ρ(h)x) = ρ(gh)x
-- statement:
--   Let a group $\mathfrak G$ act on a domain $\Omega$. There is a real linear representation $\rho$ of $\mathfrak G$ on the space of real signals $X(\Omega) = \{x : \Omega \to \mathbb R\}$, that is, a group homomorphism from $\mathfrak G$ into the linear maps of $X(\Omega)$, whose operators are the action (3):
--   $$\rho(\mathfrak g)x(u) = x(\mathfrak g^{-1} u), \qquad (\rho(\mathfrak g)(\rho(\mathfrak h)x))(u) = (\rho(\mathfrak g\mathfrak h)x)(u)$$
--   for all $\mathfrak g, \mathfrak h \in \mathfrak G$, signals $x$ and points $u \in \Omega$.
--
--   This is the book's passage from group actions on the domain to group representations on signal spaces.
--
--   **Formalization Note** The representation is Mathlib's `Representation ℝ G (Ω → ℝ)`, a monoid homomorphism into the linear endomorphisms; $\Omega$ may be infinite, in which case $\rho(\mathfrak g)$ is a linear operator rather than a matrix, as the book's side-note on p. 15 says.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.1, p. 15, "Written in the language of group representations ..."

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

namespace GeomDL.Blueprint

/-- Bronstein et al., §3.1, p. 15: "Written in the language of group representations, the action
of G on signals x ∈ X(Ω) is defined as ρ(g)x(u) = x(g⁻¹u). We again verify that
(ρ(g)(ρ(h)x))(u) = (ρ(gh)x)(u)." There is a real linear representation `ρ` of `G` on `Ω → ℝ`
(a monoid hom `G →* ((Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))`) whose operators are the action (3), and
`ρ(g)(ρ(h)x) = ρ(gh)x`. -/
theorem exists_representation_act {G Ω : Type*} [Group G] [MulAction G Ω] :
    ∃ ρ : Representation ℝ G (Ω → ℝ),
      (∀ (g : G) (x : Ω → ℝ) (u : Ω), ρ g x u = x (g⁻¹ • u)) ∧
      (∀ (g h : G) (x : Ω → ℝ), ρ g (ρ h x) = ρ (g * h) x) := by sorry

end GeomDL.Blueprint
