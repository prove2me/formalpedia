-- Prove2me | Theorems.Thm_Hirsch_gdist_reach
-- name    : Hirsch.gdist_reach
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:47.79172+00:00
-- url     : https://prove2.me/theorems/705d50b3-c801-4923-9699-abf020a781f3
-- title:
--   The graph distance between two vertices of a bounded H-polytope is attained by a walk
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i<n\}$ be a bounded H-polytope and let $u,v$ be vertices (extreme points) of $P$. Write $\mathrm{gdist}_P(u,v)$ for the combinatorial distance in the vertex-edge graph of $P$: the least $L$ such that there is a walk of exactly $L$ steps from $u$ to $v$, each step stationary or along an edge (`Reach`, from the definition `Hirsch_walk`). Then this least length is attained:
--
--   $$\mathrm{Reach}\bigl(P,\ \mathrm{gdist}_P(u,v),\ u,\ v\bigr).$$
--
--   The content is that the set of walk lengths is nonempty, i.e. that the graph of a bounded polytope is connected (Balinski; on the platform, `Hirsch.face_connected` or `Hirsch.graph_connected_general`), after which the infimum of a nonempty set of naturals is a member. This is the basic bridge between the distance function $\mathrm{gdist}$ and explicit walks, used by every layer-by-distance argument.
--
--   **Formalization Note** `gdist` is defined as `sInf` of the set of walk lengths and takes the junk value $0$ when no walk exists; boundedness is what rules that case out here.
-- source:
--   Connectivity of the graph of a polytope: M. Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961) 431-434; Prove2Me theorems Hirsch.face_connected (ca7052f3-8364-4864-857f-55df4f138c51) and Hirsch.graph_connected_general (8b17b820-f7a3-42e4-89a3-efd89fad4f3b). Distance/walk vocabulary: definition Hirsch_walk.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk

open scoped RealInnerProductSpace

namespace Hirsch

theorem gdist_reach (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) :
    Reach (Hpoly a b) (gdist (Hpoly a b) u v) u v := by sorry

end Hirsch
