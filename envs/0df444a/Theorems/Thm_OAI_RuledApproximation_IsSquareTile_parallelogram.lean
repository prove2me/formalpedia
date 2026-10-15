-- Prove2me | Theorems.Thm_OAI_RuledApproximation_IsSquareTile_parallelogram
-- name    : OAI.RuledApproximation.IsSquareTile.parallelogram
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:01:25.260341+00:00
-- url     : https://prove2.me/theorems/d33399fc-e4a9-423a-9a21-a65e6c06e45f
-- title:
--   Every square tile is a parallelogram
-- statement:
--   Let $Q=[-\tfrac12,\tfrac12]^2$ be the centred unit square of the Euclidean plane. A *square tile* is a set $T=\{c+a\,Rx : x\in Q\}$ with $c\in\mathbb{R}^2$, $R$ a linear isometry of the Euclidean plane and $a>0$, i.e. a congruent copy of a square of side $a$. A subset $P$ of the plane is a *parallelogram* if $P=\{c'+s\,x+t\,y : s,t\in[0,1]\}$ for some $c'$ and some linearly independent vectors $x,y$.
--
--   **Theorem.** Every square tile is a parallelogram: if $T=\{c+aRx : x\in Q\}$ with $c\in\mathbb{R}^2$, $R$ a linear isometry and $a>0$, then there are $c'\in\mathbb{R}^2$ and linearly independent $x,y\in\mathbb{R}^2$ with
--   $$T=\{c'+s\,x+t\,y : s,t\in[0,1]\}.$$
--
--   In the nilpotent case of the covering theorem the cylinders are built over square tiles; this lemma shows that they are in particular parallelogram cylinders, the cylinder shape used in the main covering statements.
--
--   **Formalization Note** Square tiles are `IsSquareTile T`, with `unitSquare = {x | ∀ i, |x i| ≤ 1/2}` in `EuclideanSpace ℝ (Fin 2)`; the conclusion is `IsParallelogram T`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SquareCover.lean#L192-L204

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.IsSquareTile.parallelogram {T : Set Plane} (hT : IsSquareTile T) :
    IsParallelogram T := by sorry
