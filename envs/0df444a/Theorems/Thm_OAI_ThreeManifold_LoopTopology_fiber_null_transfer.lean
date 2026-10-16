-- Prove2me | Theorems.Thm_OAI_ThreeManifold_LoopTopology_fiber_null_transfer
-- name    : OAI.ThreeManifold.LoopTopology.fiber_null_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:12:48.469135+00:00
-- url     : https://prove2.me/theorems/1a3529ab-5293-446a-abe5-7c33f538eaf9
-- title:
--   Triviality of the image of a fibre loop is independent of the base point along a path
-- statement:
--   Let $X$, $Y$, $Z$ be topological spaces and $F:X\times Y\to Z$ a continuous map. Fix $y\in Y$ and a class $\beta\in\pi_1(Y,y)$. For $x\in X$ let $\iota_x(\beta)\in\pi_1(X\times Y,(x,y))$ be the class of the loop $s\mapsto(x,b(s))$, where $b$ represents $\beta$. Equivalently, $\iota_x(\beta)$ is the image of $(1,\beta)$ under the canonical isomorphism $\pi_1(X,x)\times\pi_1(Y,y)\cong\pi_1(X\times Y,(x,y))$. Write $F_*$ for the induced homomorphisms on fundamental groups.
--
--   **Theorem.** If $x_0,x_1\in X$ are joined by a path in $X$, then
--   $$
--   F_*\big(\iota_{x_0}(\beta)\big)=1\ \text{in }\pi_1\big(Z,F(x_0,y)\big)\quad\Longleftrightarrow\quad F_*\big(\iota_{x_1}(\beta)\big)=1\ \text{in }\pi_1\big(Z,F(x_1,y)\big).
--   $$
--
--   So whether a "fibre loop" $\{x\}\times b$ becomes null-homotopic after applying $F$ depends only on the path component of $x$. This allows nontriviality of fibre classes to be checked at a single convenient base point.
--
--   **Formalization Note** The class $\iota_x(\beta)$ is `pair 1 b`, the product class $(1,\beta)$ in `FundamentalGroup (X×Y) (x,y)`, and $F_*$ is `FundamentalGroup.map F`. The path from $x_0$ to $x_1$ is an explicit `Path x₀ x₁`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/FundamentalGroup.lean#L344-L369

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
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup

open OAI OAI.ThreeManifold OAI.ThreeManifold.LoopTopology
open Set Topology
open Path.Homotopic
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y}

theorem OAI.ThreeManifold.LoopTopology.fiber_null_transfer (F : C(X×Y,Z)) {x₀ x₁ : X} (p : Path x₀ x₁)
    (b : FundamentalGroup Y y) :
    FundamentalGroup.map F (x₀,y) (pair 1 b) = 1 ↔
      FundamentalGroup.map F (x₁,y) (pair 1 b) = 1 := by sorry
