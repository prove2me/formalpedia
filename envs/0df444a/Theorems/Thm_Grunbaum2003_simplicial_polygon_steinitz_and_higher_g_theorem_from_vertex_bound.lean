-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_polygon_steinitz_and_higher_g_theorem_from_vertex_bound
-- name    : Grunbaum2003.simplicial_polygon_steinitz_and_higher_g_theorem_from_vertex_bound
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-08T01:30:23.662743+00:00
-- url     : https://prove2.me/theorems/94fef9f4-1ccd-463e-b656-d0ad12de71fa
-- title:
--   Polygon ($d=2$), Steinitz ($d=3$), and higher ($d \ge 4$) simplicial $g$-theorem given the exposed-vertex count and lower bound $f_0(P) \ge d + 1$
-- statement:
--   Given the proved exposed-vertex cardinal identity $f_0(P) = \#\{x \in \mathbb{R}^d \mid \operatorname{IsExposed}_{\mathbb{R}}(P, \{x\})\}$ and the sharp lower bound $f_0(P) \ge d + 1$ for every $d$-polytope $P \subseteq \mathbb{R}^d$ (`polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound`), this theorem states the remaining geometric $f$-vector characterizations for polygons ($d = 2$, $f_1 = f_0 = n + 3$), simplicial $3$-polytopes ($d = 3$, $f_0 = n + 4$, $f_1 = 3n + 6$, $f_2 = 2n + 4$), and higher dimensions ($d \ge 4$).
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_polygon_steinitz_and_higher_g_theorem_from_vertex_bound
    (hVertexBound : ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
      faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
      (IsDPolytope P → d + 1 ≤ faceCount P 0)) :
    (∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 2 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 2, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3)) ∧
    (∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 3 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 3, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4)) ∧
    (∀ (d : ℕ), 4 ≤ d → ∀ (f : Fin (d + 1) → ℤ), f 0 = 1 →
      ((∃ P : Set (Fin d → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ k : Fin (d + 1),
          f k = ∑ j ∈ Finset.range (d / 2 + 1),
            (g j : ℤ) * gTheoremMatrix d j k.val)) := by sorry

end Grunbaum2003
