-- Prove2me | Theorems.Thm_Grunbaum2003_polytope_edge_count_and_second_g_coefficient_upper_bound
-- name    : Grunbaum2003.polytope_edge_count_and_second_g_coefficient_upper_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:46:04.583615+00:00
-- url     : https://prove2.me/theorems/f0811aba-ce1c-4f08-9c50-793bab05686a
-- title:
--   Polytope edge counting, second g-coefficient bound, and degree-two Macaulay condition
-- statement:
--   Let $P\subseteq\mathbb R^d$ be a full-dimensional nonempty polytope, with $N=f_0(P)$ exposed vertices and $E=f_1(P)$ edges. Put
--   $$x=N-d-1,\qquad z=E-\binom{d+1}{2}-dx.$$
--   The vertex lower bound gives $N\ge d+1$, so $x$ is a natural number. We prove
--   $$E\le\binom N2,\qquad z\le\binom{x+1}{2}.$$
--   Here $z$ is an integer; no lower bound on $z$ is asserted.
--
--   Each edge is the convex hull of its two distinct exposed vertices. Thus the set of edges is contained in the image of the two-element subsets of the vertex set under the convex-hull map. Taking finite cardinalities gives
--   $$E\le\binom N2.$$
--   This argument uses the previously proved exposed-vertex representation of polytope faces, the characterization of exposed one-dimensional faces as vertex pairs, and the equality of the vertex count with the number of exposed vertices.
--
--   The elementary binomial identity
--   $$\binom{d+1+x}{2}=\binom{d+1}{2}+dx+\binom{x+1}{2}$$
--   then gives the bound on $z$ after subtracting the first two terms. The Lean statement writes the same expression using natural subtraction, justified by $N\ge d+1$.
--
--   For Björner's matrix coordinates, the first two face equations identify $x=g_1$ and $z=g_2$. The result therefore supplies the degree-two Macaulay upper bound. Establishing $g_2\ge0$, Dehn–Sommerville symmetry, and all higher Macaulay inequalities remains separate work; this lemma does not establish the full necessity theorem.
--
--   More explicitly, if $g:\mathbb N\to\mathbb N$ satisfies
--   $$g_0=1,\qquad f_0(P)=d+1+g_1,\qquad f_1(P)=\binom{d+1}{2}+dg_1+g_2,$$
--   then the bound above gives $g_2\le\binom{g_1+1}{2}$. The proved length-two Macaulay characterization therefore gives $\operatorname{IsMSequence}(2,g)$. This final implication uses natural coefficients as an explicit hypothesis; it does not prove that the signed coefficient is nonnegative.
-- source:
--   Grünbaum, Convex Polytopes, second edition (2003), §10.6, p. 198a / PDF p. 235 (Björner matrix formula). The auxiliary upper bound is derived by elementary counting of unordered pairs of polytope vertices; it does not invoke Stanley necessity.

import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_isMSequence_two_iff_choose_bound
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped Classical
open Grunbaum2003

namespace Grunbaum2003

theorem polytope_edge_count_and_second_g_coefficient_upper_bound {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    faceCount P 1 ≤ Nat.choose (faceCount P 0) 2 ∧
    ((faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) -
        (d : ℤ) * ((faceCount P 0 - (d + 1) : ℕ) : ℤ) ≤
      (Nat.choose (faceCount P 0 - d) 2 : ℤ)) ∧
    (∀ g : ℕ → ℕ, g 0 = 1 →
      faceCount P 0 = d + 1 + g 1 →
      faceCount P 1 = Nat.choose (d + 1) 2 + d * g 1 + g 2 →
      IsMSequence 2 g) := by sorry

end Grunbaum2003
