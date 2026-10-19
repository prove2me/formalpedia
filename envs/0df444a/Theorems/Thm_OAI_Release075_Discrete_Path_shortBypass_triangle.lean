-- Prove2me | Theorems.Thm_OAI_Release075_Discrete_Path_shortBypass_triangle
-- name    : OAI.Release075.Discrete.Path.shortBypass_triangle
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:33:37.808929+00:00
-- url     : https://prove2.me/theorems/c988a27c-0250-4b02-8387-1fb15ea24e11
-- title:
--   Fat points of thin triangles have short bypasses
-- statement:
--   Let $d$ be a metric on $V$ with values in $\mathbb N$, geodesic in the sense that any two points are joined by a discrete path of length $d(a,b)$ (consecutive points at distance $\le1$). For geodesics $p:a\to b$, $q:b\to c$, $s:a\to c$, the triangle is $T$-near if every point of each side lies within $T$ of a point of one of the other two sides. A short bypass of size $K$ around $o$ at radius $T$ is a geodesic through $o$ together with a return path between its endpoints that stays at distance $\ge T$ from $o$, of total length at most $K$. If the triangle is $T$-near and a point $o$ on $p$ has distance at least $T$ from every point of $q$ and $s$, then there is a short bypass around $o$ at radius $T$ of size
--   $$
--   1000\,(T+1).
--   $$
--
--   The constant is not optimized; only its linearity in $T$ matters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean#L243-L272

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

theorem OAI.Release075.Discrete.Path.shortBypass_triangle (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T : ℕ} (hthin : TriangleNear T p q s) {o : V} (ho : p.Mem o)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist o x) :
    ShortBypass M T o (1000*(T+1)) := by sorry
