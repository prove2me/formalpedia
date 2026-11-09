-- Prove2me | Theorems.Thm_MWCSherali_theorem_4_2
-- name    : MWCSherali.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:09:13.970204+00:00
-- url     : https://prove2.me/theorems/aae5615f-b204-442f-9e81-2d8a931285d9
-- title:
--   Theorem 4.2 ([Apo69]) — divergence theorem for polyhedra in $\mathbb R^3$
-- statement:
--   Let $R\subset\mathbb R^3$ be a closed and bounded polyhedron with nonempty interior, and let $g=(g_1,g_2,g_3)$ be a continuously differentiable vector field on an open neighbourhood of $R$. Then
--
--   $$\int_R\operatorname{div}g\,dx=\sum_{F\ \text{facet of}\ R}\int_Fn_F\cdot g\,dS,$$
--
--   where $\operatorname{div}g=\sum_{i}\partial g_i/\partial x_i$, $n_F$ is the outward unit normal of the facet $F$, $dx$ is the volume element and $dS$ the surface area element. The paper cites this standard result; it is applied to the tetrahedra of the central region and to truncated tubes.
--
--   **Formalization Note** The polyhedron is $R=\{x\mid\langle n,x\rangle\le c\ \text{for all}\ (n,c)\in H\}$ for a finite set $H$ of unit normals with offsets. The surface integral over the face $R\cap\{\langle n,x\rangle=c\}$ is an integral over the plane $\{cn+y\mid y\perp n\}$ against the Lebesgue measure of the 2-dimensional inner product space $n^\perp$.
--
--   Differences from the source:
--   - reading: "closed and bounded polyhedron" → R = {x | ⟪n, x⟫ ≤ c for all (n, c) ∈ H}, H a finite set of (unit normal, offset) pairs, bounded with nonempty interior; reason: polyhedron in the linear-programming sense, the sense in which the paper speaks of facets; the theorem is applied only to convex polytopes (tetrahedra, truncated tubes)
--   - encoding: sum over the facets F of R with outward unit normals n_F → sum over (n, c) ∈ H of the integral over R ∩ {⟪n, x⟫ = c}; reason: a non-facet face has zero area and contributes 0; distinct unit normals cannot describe the same facet
--   - encoding: surface area element dS on a facet → Lebesgue (Haar) measure of the inner product space (ℝ ∙ n)ᗮ, carried to the plane by y ↦ c n + y; reason: this is the 2-dimensional area on the plane
--   - encoding: ℝ³ and div g = Σ ∂g_i/∂x_i → EuclideanSpace ℝ (Fin 3), div g x = Σ_i (Dg(x) e_i)_i, g C¹ on an open U ⊇ R; reason: Lean convention
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 4.2, p.32

import Mathlib

namespace MWCSherali

open MeasureTheory

/-- **Theorem 4.2 (divergence theorem for polyhedra, [Apo69]).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 4.2,
p.32: "Let `R ⊂ ℝ³` be a closed and bounded polyhedron with nonempty interior, and let
`g = (g₁, g₂, g₃)` be a continuously differentiable vector field on an open neighborhood of `R`.
Then we have `∫_R div g dx = ∑_{F facet of R} ∫_F n_F · g dS`", where `div g = ∑ ∂gᵢ/∂xᵢ`, `n_F` is
the outward unit normal of the facet `F`, `dx` the volume element and `dS` the surface area
element. The paper cites this standard result and does not prove it.

**Formalization Note.**
* "Polyhedron" is read in the linear-programming sense: `R = {x | ⟪n, x⟫ ≤ c for all (n, c) ∈ H}`
  for a finite set `H` of pairs of a unit vector `n` and an offset `c`. Closedness is then
  automatic; boundedness and nonempty interior are hypotheses.
* The sum over facets is the sum over `H`: for `(n, c) ∈ H` the face `R ∩ {⟪n, x⟫ = c}` is a facet
  with outward unit normal `n` when it has positive area, and otherwise (a redundant inequality)
  contributes `0`. Distinct pairs with the same unit normal cannot both give facets, and opposite
  normals of one hyperplane would leave `R` without interior, so no facet is counted twice.
* The surface integral over `R ∩ {⟪n, x⟫ = c}` is the integral over the plane `{c n + y | y ⊥ n}`
  against the Lebesgue measure `volume` of the 2-dimensional inner product space `(ℝ ∙ n)ᗮ`,
  which is the surface area element of the plane.
* `ℝ³` is `EuclideanSpace ℝ (Fin 3)` with its Lebesgue measure; `div g x` is
  `∑ᵢ (Dg(x) eᵢ)ᵢ`. `g` is `C¹` on an open set `U ⊇ R`. -/
theorem theorem_4_2 (H : Finset (EuclideanSpace ℝ (Fin 3) × ℝ)) (hunit : ∀ p ∈ H, ‖p.1‖ = 1)
    (R : Set (EuclideanSpace ℝ (Fin 3))) (hR : R = {x | ∀ p ∈ H, inner ℝ p.1 x ≤ p.2})
    (hbdd : Bornology.IsBounded R) (hint : (interior R).Nonempty)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U) (hRU : R ⊆ U)
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (hg : ContDiffOn ℝ 1 g U) :
    ∫ x in R, ∑ i, fderiv ℝ g x (EuclideanSpace.single i 1) i =
      ∑ p ∈ H, ∫ y : (Submodule.span ℝ {p.1})ᗮ,
        R.indicator (fun x => inner ℝ p.1 (g x)) (p.2 • p.1 + (y : EuclideanSpace ℝ (Fin 3))) := by sorry

end MWCSherali
