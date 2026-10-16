-- Prove2me | Theorems.Thm_OAI_ThreeManifold_NonpositiveMetric_CNMidpoint_projection_angle
-- name    : OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.projection_angle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:59:30.999903+00:00
-- url     : https://prove2.me/theorems/a8bb14ee-cec6-4ac5-b162-b43c06396a82
-- title:
--   Obtuse-angle inequality for nearest points on midpoint-convex sets in spaces satisfying the CN inequality
-- statement:
--   Let $(X,d)$ be a metric space equipped with a *CN midpoint map* $m:X\times X\to X$, i.e. a map satisfying the Bruhat–Tits CN inequality
--   $$
--   d\big(m(x,y),z\big)^2\le\frac{d(x,z)^2+d(y,z)^2}{2}-\frac{d(x,y)^2}{4}\qquad\text{for all }x,y,z\in X .
--   $$
--   A set $S\subseteq X$ is *midpoint-convex* if $m(x,y)\in S$ whenever $x,y\in S$.
--
--   **Theorem.** Let $S\subseteq X$ be midpoint-convex, let $x\in X$, and let $p\in S$ be a nearest point of $S$ to $x$, meaning $d(x,p)\le d(x,z)$ for every $z\in S$. Then for every $q\in S$,
--   $$
--   d(x,p)^2+d(p,q)^2\le d(x,q)^2 .
--   $$
--
--   Geometrically, the angle at the foot point $p$ between $x$ and any other point $q$ of $S$ is at least a right angle. No completeness or closedness assumption is needed. The inequality implies that nearest-point projections onto midpoint-convex sets are unique and $1$-Lipschitz, and it is the basic tool for studying projections onto geodesic lines and minimal sets of isometries in nonpositively curved spaces.
--
--   **Formalization Note** The CN midpoint map is the structure `CNMidpoint X` with fields `mid` and `cn`; midpoint-convexity is `C.MidConvex S`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Convexity.lean#L137-L152

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity

open OAI OAI.ThreeManifold OAI.ThreeManifold.NonpositiveMetric OAI.ThreeManifold.NonpositiveMetric.CNMidpoint
open Set Filter Topology Function
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C

theorem OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.projection_angle {S : Set X} (hS : C.MidConvex S) {x p : X} (hp : p ∈ S)
    (hm : ∀ z ∈ S, dist x p ≤ dist x z) {q : X} (hq : q ∈ S) :
    dist x p ^2 + dist p q ^2 ≤ dist x q ^2 := by sorry
