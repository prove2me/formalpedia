-- Prove2me | Theorems.Thm_Grunbaum2003_exists_apex_beyond_simplicial_facet_preserving_proper_faces
-- name    : Grunbaum2003.exists_apex_beyond_simplicial_facet_preserving_proper_faces
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T04:41:33.729178+00:00
-- url     : https://prove2.me/theorems/09649c14-d0b1-4521-b852-b81cc39d3d66
-- title:
--   An exterior apex preserving prescribed proper faces
-- statement:
--   Let $P\subset\mathbb R^d$ be a full-dimensional simplicial polytope and $F$ a nonempty facet. Fix a supporting inequality $\varphi\le a$ whose contact set in $P$ is exactly $F$. For any finite family of proper exposed faces $G_j\ne F$, fix supporting inequalities $\psi_j\le c_j$ with those exact contact sets. Empty contact sets are allowed.
--
--   There exists $y\notin P$ such that
--
--   $$\varphi(y)>a,\qquad \psi_j(y)<c_j\quad\text{for every }j.$$
--
--   Moreover, for $Q=\operatorname{conv}(P\cup\{y\})$, each $G_j$ remains an exposed face of $Q$, while $F$ is no longer an exposed face of $Q$.
--
--   The supporting functionals are prescribed inputs, so the construction can be combined with a chosen halfspace presentation. This supplies the apex and old-face preservation needed for stellar subdivision.
-- source:
--   Auxiliary support-plane lemma for Grunbaum2003.exists_stellar_subdivision_cone_decomposition, https://prove2.me/theorems/66fedc85-e2bf-44b8-9b3b-9e7d0d908ec9 (source: Grünbaum, Convex Polytopes, 2003, Chapter 10). This precise auxiliary statement and its elementary proof are supplied here; it is not a verbatim theorem from the book.

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003

theorem exists_apex_beyond_simplicial_facet_preserving_proper_faces {d m : ℕ}
    {P F : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d)
    (G : Fin m → Set (Fin d → ℝ))
    (hG : ∀ j, IsExposed ℝ P (G j))
    (hGproper : ∀ j, G j ≠ P)
    (hGF : ∀ j, G j ≠ F)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ a) (hFeq : F = {x ∈ P | φ x = a})
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hother_bound : ∀ j x, x ∈ P → ψ j x ≤ c j)
    (hGeq : ∀ j, G j = {x ∈ P | ψ j x = c j}) :
    ∃ y : Fin d → ℝ, y ∉ P ∧ a < φ y ∧ (∀ j, ψ j y < c j) ∧
      (∀ j, IsExposed ℝ (convexHull ℝ (insert y P)) (G j)) ∧
      ¬ IsExposed ℝ (convexHull ℝ (insert y P)) F := by sorry

end Grunbaum2003
