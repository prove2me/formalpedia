-- Prove2me | Theorems.Thm_OAI_Release075_Discrete_Path_shortBypass_center
-- name    : OAI.Release075.Discrete.Path.shortBypass_center
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:32:59.555986+00:00
-- url     : https://prove2.me/theorems/1ed68b9a-03da-4cdc-857d-d7f05266f1f6
-- title:
--   Short bypasses around points near the centre of a thin triangle
-- statement:
--   Let $d$ be a metric on $V$ with values in $\mathbb N$. A discrete path from $a$ to $b$ has length $n$ and points $p_0=a,\dots,p_n=b$ with consecutive points at distance $\le1$; it is geodesic if $n=d(a,b)$. For geodesic paths $p:a\to b$, $q:b\to c$, $s:a\to c$, the side $p$ is $T$-near the others if every point of $p$ is within distance $T$ of a point of $q$ or $s$; the triangle is $T$-near if all three sides are. A short bypass of size $K$ around $o$ at radius $T$ is a geodesic through $o$ together with a return path that stays at distance $\ge T$ from $o$, of total length at most $K$. Assume the metric is geodesic, the triangle is $T$-near, $R\ge4T+2$, and $o=p_t$ is at distance $\ge T$ from $q$ and $s$ and lies within $4R$ of the internal point of $p$ in both directions:
--   $$
--   \tfrac12(|p|+|s|-|q|)\le t+4R,\qquad \tfrac12(|p|+|q|-|s|)\le|p|-t+4R .
--   $$
--   Then there is a short bypass of size $60R$ around $o$ at radius $T$.
--
--   Together with the arm case, every point far from the other sides of a thin triangle admits a short bypass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean#L130-L241

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

theorem OAI.Release075.Discrete.Path.shortBypass_center (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T R t : ℕ} (hR : 4*T+2 ≤ R) (ht : t ≤ p.length)
    (hthin : TriangleNear T p q s)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist (p.point t) x)
    (hcenter₁ : (p.length+s.length-q.length)/2 ≤ t+4*R)
    (hcenter₂ : (p.length+q.length-s.length)/2 ≤ p.length-t+4*R) :
    ShortBypass M T (p.point t) (60*R) := by sorry
