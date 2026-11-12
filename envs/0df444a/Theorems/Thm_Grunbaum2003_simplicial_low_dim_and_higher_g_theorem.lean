-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_low_dim_and_higher_g_theorem
-- name    : Grunbaum2003.simplicial_low_dim_and_higher_g_theorem
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T19:08:51.621081+00:00
-- url     : https://prove2.me/theorems/a105e5d5-4d1c-48a5-a8ab-e74ab19d33d5
-- title:
--   Geometric $f$-vector characterization for polygons ($d=2$), simplicial $3$-polytopes ($d=3$), and higher $g$-theorem ($d \ge 4$)
-- statement:
--   This theorem pairs with the proved low-dimensional Macaulay and $g$-matrix characterization `g_theorem_rhs_low_dim_iff` to decompose `simplicial_g_theorem_ge_two` into explicit geometric $f$-vector characterizations in dimensions $d = 2$ and $d = 3$ and the higher-dimensional regime $d \ge 4$:
--
--   1. **Polygons ($d = 2$):** For $f : \operatorname{Fin} 3 \to \mathbb{Z}$ with $f(0) = 1$, there exists a simplicial $2$-polytope $P \subseteq \mathbb{R}^2$ with $(f_0(P), f_1(P)) = (f(1), f(2))$ if and only if $f(1) = n + 3$ and $f(2) = n + 3$ for some $n \in \mathbb{N}$.
--   2. **Simplicial $3$-polytopes ($d = 3$, Steinitz's characterization):** For $f : \operatorname{Fin} 4 \to \mathbb{Z}$ with $f(0) = 1$, there exists a simplicial $3$-polytope $P \subseteq \mathbb{R}^3$ with $(f_0(P), f_1(P), f_2(P)) = (f(1), f(2), f(3))$ if and only if there exists $n \in \mathbb{N}$ such that
--      $$
--      f(1) = n + 4, \qquad f(2) = 3n + 6, \qquad f(3) = 2n + 4.
--      $$
--   3. **Higher dimensions ($d \ge 4$, where $\lfloor d/2 \rfloor \ge 2$):** The Billera–Lee–Stanley $g$-theorem equivalence holds for all $d \ge 4$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_low_dim_and_higher_g_theorem :
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
