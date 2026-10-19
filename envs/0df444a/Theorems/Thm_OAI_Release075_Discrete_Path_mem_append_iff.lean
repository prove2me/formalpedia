-- Prove2me | Theorems.Thm_OAI_Release075_Discrete_Path_mem_append_iff
-- name    : OAI.Release075.Discrete.Path.mem_append_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:24:34.525136+00:00
-- url     : https://prove2.me/theorems/3c2fabee-22d8-40ea-87a5-b3402b31cb3c
-- title:
--   Points of a concatenated discrete path
-- statement:
--   Let $d$ be a metric on $V$ with values in $\mathbb N$. A discrete path from $a$ to $b$ has length $n$ and points $p_0=a,\dots,p_n=b$ with consecutive points at distance $\le1$; it is geodesic if $n=d(a,b)$. For paths $p:a\to b$ and $q:b\to c$ and a point $x$,
--   $$
--   x\in p\cdot q\iff x\in p\ \text{or}\ x\in q .
--   $$
--
--   Here $x\in p$ means $x=p_i$ for some $i$ up to the length of $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean#L118-L131

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
variable {V : Type} (M : Metric V)
variable {M} {a b c : V}

theorem OAI.Release075.Discrete.Path.mem_append_iff (p : Path M a b) (q : Path M b c) (x : V) :
    (p.append q).Mem x ↔ p.Mem x ∨ q.Mem x := by sorry
