-- Prove2me | Theorems.Thm_Grunbaum2003_exists_vertex_cut_level
-- name    : Grunbaum2003.exists_vertex_cut_level
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:35:50.284981+00:00
-- url     : https://prove2.me/theorems/f120a17f-c3bf-44d0-b2a9-6105cc6dfc25
-- title:
--   A cutoff hyperplane separating an exposed vertex from all other vertices
-- statement:
--   Every nonempty full-dimensional polytope $P$ has an exposed vertex $v$, an exposing continuous linear functional $\ell$, and a level $\alpha<\ell(v)$ such that $\ell(x)\le\ell(v)$ for every $x\in P$, while $\ell(w)<\alpha$ for every other exposed vertex $w$.
--
--   For each such $w$, the segment from $v$ to $w$ crosses the hyperplane $\ell(x)=\alpha$ at a parameter strictly between zero and one. The same functional and level work for all other vertices. This supplies the cutting hyperplane in the vertex-figure construction; it does not yet assert the full boundary-refinement theorem.
-- source:
--   Grünbaum, On the facial structure of convex polytopes (1965), Theorem1* induction, pp.559–560, vertex figure at an exposed vertex. https://faculty.washington.edu/moishe/branko/BG52.Facial%20structure.pdf

import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_vertex_cut_level (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    ∃ v : Fin d → ℝ, IsExposed ℝ P {v} ∧
      ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
        ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
          l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α := by sorry

end Grunbaum2003
