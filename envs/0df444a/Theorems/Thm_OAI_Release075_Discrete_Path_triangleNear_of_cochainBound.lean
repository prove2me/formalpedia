-- Prove2me | Theorems.Thm_OAI_Release075_Discrete_Path_triangleNear_of_cochainBound
-- name    : OAI.Release075.Discrete.Path.triangleNear_of_cochainBound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:34:16.324988+00:00
-- url     : https://prove2.me/theorems/ee998cbf-6875-46e9-9400-3ee3197366fe
-- title:
--   A linear cochain bound makes geodesic triangles uniformly thin
-- statement:
--   Let $d$ be a metric on $V$ with values in $\mathbb N$, geodesic in the sense that any two points are joined by a discrete path of length $d(a,b)$ (consecutive points at distance $\le1$). The metric has cochain bound $B$ if for all $o,a\in V$ and $R\in\mathbb N$, every closed discrete path $p$ satisfies $\bigl|\int_p\omega\bigr|\le B\cdot\mathrm{length}(p)$, where $\omega(x,y)=(\tau(x)+\tau(y))(d(a,y)-d(a,x))$ and $\tau(x)=\max(0,R-d(o,x))$. If the metric has cochain bound $B$, then every geodesic triangle is $T$-near with
--   $$
--   T=10000\,(B+1).
--   $$
--
--   So a discrete linear isoperimetric inequality for these tent forms implies hyperbolicity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean#L340-L374

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles

open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path
variable {V : Type} {M : Metric V}
variable {a b c : V}

theorem OAI.Release075.Discrete.Path.triangleNear_of_cochainBound (hgeo : GeodesicSpace M) {B : ℕ}
    (hB : CochainBound M B) {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) :
    TriangleNear (10000*(B+1)) p q s := by sorry
