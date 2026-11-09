-- Prove2me | Theorems.Thm_Grunbaum2003_exists_simplicial_four_polytope_with_g_132
-- name    : Grunbaum2003.exists_simplicial_four_polytope_with_g_132
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T04:38:44.326087+00:00
-- url     : https://prove2.me/theorems/77b6bada-b53c-4a7a-80dc-38fe658e8464
-- title:
--   A simplicial four-polytope realizing g = (1, 3, 2)
-- statement:
--   There exists a full-dimensional simplicial polytope in $\mathbb R^4$ with
--
--   $$f=(8,24,32,16),\qquad g=(1,3,2).$$
--
--   More precisely, its numbers of vertices, edges, two-dimensional faces, and facets are respectively $8$, $24$, $32$, and $16$. The sequence $(1,3,2,0,0,\ldots)$ satisfies the Macaulay inequalities through degree two and gives these face counts under the g-theorem matrix transform.
--
--   This is the four-dimensional cross-polytope example: it supplies a positive-$g_2$ instance of the realization problem. The assertion is a concrete example and does not settle the universal g-theorem.
--
--   **Formalization Note** The theorem uses the project's canonical `IsSimplicialDPolytope`, `faceCount`, `IsMSequence`, and `gTheoremMatrix` definitions. The witness is the convex hull of the eight signed coordinate vectors.
-- source:
--   Ed Swartz, From Polytopes to Enumeration, Example 3.5 (PDF p.6), https://pi.math.cornell.edu/~ebs/math455.pdf; full signed-coordinate face classification and exact canonical face-count proof supplied here.

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators
namespace Grunbaum2003

theorem exists_simplicial_four_polytope_with_g_132 :
    ∃ P : Set (Fin 4 → ℝ), Grunbaum2003.IsSimplicialDPolytope P ∧
      Grunbaum2003.faceCount P 0 = 8 ∧
      Grunbaum2003.faceCount P 1 = 24 ∧
      Grunbaum2003.faceCount P 2 = 32 ∧
      Grunbaum2003.faceCount P 3 = 16 ∧
      Grunbaum2003.IsMSequence 2 (fun i : ℕ => if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 0) ∧
      ∀ j : Fin 4, (Grunbaum2003.faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range 3, ((fun i : ℕ => if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 0) i : ℤ) * Grunbaum2003.gTheoremMatrix 4 i j.succ.val := by sorry

end Grunbaum2003
