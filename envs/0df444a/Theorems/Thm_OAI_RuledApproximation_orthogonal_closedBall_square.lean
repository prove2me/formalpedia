-- Prove2me | Theorems.Thm_OAI_RuledApproximation_orthogonal_closedBall_square
-- name    : OAI.RuledApproximation.orthogonal_closedBall_square
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:58:13.413778+00:00
-- url     : https://prove2.me/theorems/5264a6cb-901a-4d87-b35c-b5bd02c1396f
-- title:
--   Coordinate squares in an orthonormal frame are square tiles
-- statement:
--   Let $Q=[-\tfrac12,\tfrac12]^2$ be the centred unit square of the Euclidean plane. A *square tile* is a set $T=\{c+a\,Rx : x\in Q\}$ with $c\in\mathbb{R}^2$, $R$ a linear isometry of the Euclidean plane and $a>0$, i.e. a congruent copy of a square of side $a$. For a linear isometry $R$ of the Euclidean plane, the *orthogonal frame* $M_R$ maps a coordinate vector $x=(x_1,x_2)$ to the point $M_R(x)=R(x_1e_1+x_2e_2)$ of the Euclidean plane; on the coordinate side we use the maximum norm, whose closed balls are the coordinate squares $\bar B_\infty(b,a)=[b_1-a,b_1+a]\times[b_2-a,b_2+a]$.
--
--   **Theorem.** For every linear isometry $R$ of the Euclidean plane, every $b\in\mathbb{R}^2$ and every $a>0$, the image $M_R(\bar B_\infty(b,a))$ is a square tile: there are $c\in\mathbb{R}^2$, a linear isometry $R'$ and $a'>0$ with
--   $$M_R\bigl([b_1-a,b_1+a]\times[b_2-a,b_2+a]\bigr)=\{c+a'R'x : x\in Q\}.$$
--
--   In the nilpotent case of the covering argument the local covers are built from coordinate squares around grid points, expressed in an orthonormal frame adapted to the derivative. This lemma identifies their images in the physical plane as square tiles, which is the form of footprint required by the nilpotent covering statement.
--
--   **Formalization Note** $M_R$ is `orthogonalFrame R : Coordinates ≃L[ℝ] Plane`, the composition of the identification `(EuclideanSpace.equiv (Fin 2) ℝ).symm` with `R`; `Coordinates = Fin 2 → ℝ` carries the sup norm, so `closedBall b a` is the coordinate square. Square tiles are `IsSquareTile`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/NilpotentLattice.lean#L140-L173

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

theorem OAI.RuledApproximation.orthogonal_closedBall_square (R : Plane ≃ₗᵢ[ℝ] Plane) (b : Coordinates)
    {a : ℝ} (ha : 0 < a) :
    IsSquareTile (orthogonalFrame R '' closedBall b a) := by sorry
