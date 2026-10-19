-- Prove2me | Theorems.Thm_OAI_Release075_Discrete_Path_synchronous
-- name    : OAI.Release075.Discrete.Path.synchronous
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:27:22.655339+00:00
-- url     : https://prove2.me/theorems/6714c5c6-850e-4912-ac48-a5ca4486e75f
-- title:
--   Synchronous points on two sides of a thin triangle are close
-- statement:
--   Let $d$ be a metric on $V$ with values in $\mathbb N$. A discrete path from $a$ to $b$ has length $n$ and points $p_0=a,\dots,p_n=b$ with consecutive points at distance $\le1$; it is geodesic if $n=d(a,b)$. For geodesic paths $p:a\to b$, $q:b\to c$, $s:a\to c$, the side $p$ is $T$-near the others if every point of $p$ is within distance $T$ of a point of $q$ or $s$; the triangle is $T$-near if all three sides are. A short bypass of size $K$ around $o$ at radius $T$ is a geodesic through $o$ together with a return path that stays at distance $\ge T$ from $o$, of total length at most $K$. If $p$ is $T$-near $q\cup s$ and $i\le(|p|+|s|-|q|)/2$ (the Gromov product at $a$), then
--   $$
--   d(p_i,s_i)\le4T+2 .
--   $$
--
--   This is the elementary comparison of a thin triangle with its tripod.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean#L319-L380

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

open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path
variable {V : Type} {M : Metric V}
variable {a b c d e f : V}

theorem OAI.Release075.Discrete.Path.synchronous {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) {T i : ℕ}
    (hthin : SideNear T p q s) (hi : i ≤ (p.length+s.length-q.length)/2) :
    M.dist (p.point i) (s.point i) ≤ 4*T+2 := by sorry
