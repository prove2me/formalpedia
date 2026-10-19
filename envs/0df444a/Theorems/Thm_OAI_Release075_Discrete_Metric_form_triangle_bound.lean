-- Prove2me | Theorems.Thm_OAI_Release075_Discrete_Metric_form_triangle_bound
-- name    : OAI.Release075.Discrete.Metric.form_triangle_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:26:01.905493+00:00
-- url     : https://prove2.me/theorems/ec0cbb83-257d-4a82-8065-272dcdb8ade7
-- title:
--   The tent form has bounded coboundary on small triangles
-- statement:
--   Let $d$ be a metric on $V$ with values in $\mathbb N$. A discrete path from $a$ to $b$ has length $n$ and points $p_0=a,\dots,p_n=b$ with consecutive points at distance $\le1$; it is geodesic if $n=d(a,b)$. For $o,a\in V$ and $R\in\mathbb N$ put $\tau(x)=\max(0,R-d(o,x))$ and $\omega(x,y)=(\tau(x)+\tau(y))\bigl(d(a,y)-d(a,x)\bigr)$. If $d(x,y)\le1$ and $d(z,x)\le1$, then
--   $$
--   \bigl|\omega(x,y)+\omega(y,z)+\omega(z,x)\bigr|\le2 .
--   $$
--
--   So the coboundary of $\omega$ on every triangle of the Cayley complex is at most $2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean#L234-L256

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

open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Metric
variable {V : Type} (M : Metric V)
variable {M}

theorem OAI.Release075.Discrete.Metric.form_triangle_bound (o a x y z : V) (R : ℕ)
    (hxy : M.dist x y ≤ 1) (_hyz : M.dist y z ≤ 1) (hzx : M.dist z x ≤ 1) :
    |M.form o a R x y+M.form o a R y z+M.form o a R z x| ≤ 2 := by sorry
