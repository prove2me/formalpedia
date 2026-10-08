-- Prove2me | Theorems.Thm_GeometryOfGraphs_Cube_theorem_5_7
-- name    : GeometryOfGraphs.Cube.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:01.318412+00:00
-- url     : https://prove2.me/theorems/c116f462-b432-44bc-8f8f-3027210f6f46
-- title:
--   Theorem 5.7 — isometric dimension as minimum implementing rank
-- statement:
--   Let $G$ be a finite connected graph. Among all real matrices $M$ that implement $G$, with the number of columns allowed to vary, its isometric dimension is the smallest matrix rank:
--
--   $$
--   \dim(G)=\min\{\operatorname{rank}(M): M\text{ implements }G\}.
--   $$
--
--   This characterizes the geometric invariant by linear algebra and is used for lower bounds such as the even-cycle calculation.
--
--   **Formalization Note** The implementation condition uses coordinatewise bounds plus attainment, so a zero-column matrix is permitted for a one-vertex graph.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 232, Theorem 5.7; https://doi.org/10.1007/BF01200757

import Definitions.Def_GeometryOfGraphs_Cube_IsometricDimension
import Definitions.Def_GeometryOfGraphs_Cube_Implements

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- Theorem 5.7: isometric dimension is the least rank of an implementing matrix. -/
theorem theorem_5_7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    isoDim G = sInf {k : ℕ | ∃ (r : ℕ) (M : Matrix V (Fin r) ℝ),
      Implements G M ∧ M.rank = k} := by sorry

end GeometryOfGraphs.Cube
