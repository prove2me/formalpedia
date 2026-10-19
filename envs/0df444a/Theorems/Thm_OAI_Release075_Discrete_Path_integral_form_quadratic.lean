-- Prove2me | Theorems.Thm_OAI_Release075_Discrete_Path_integral_form_quadratic
-- name    : OAI.Release075.Discrete.Path.integral_form_quadratic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:29:16.446335+00:00
-- url     : https://prove2.me/theorems/0ee46d9a-36d8-4ad7-ba46-d6076c498163
-- title:
--   The tent form integrates quadratically along a geodesic
-- statement:
--   Let $d$ be a metric on $V$ with values in $\mathbb N$. A discrete path from $a$ to $b$ has length $n$ and points $p_0=a,\dots,p_n=b$ with consecutive points at distance $\le1$; it is geodesic if $n=d(a,b)$. Let $p$ be a geodesic from $a$ to $b$, $o=p_t$ a point on it with $d(o,b)\ge T$, and $\omega$ the tent form with centre $o$, base point $a$ and radius $T$:
--   $$
--   \omega(x,y)=(\tau(x)+\tau(y))(d(a,y)-d(a,x)),\quad\tau(x)=\max(0,T-d(o,x)).
--   $$
--   Then
--   $$
--   \Bigl\lfloor\tfrac T2\Bigr\rfloor^2\le\int_p\omega .
--   $$
--
--   Combined with a linear bound on such integrals over closed paths, this forces bypasses to be long.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean#L394-L437

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

theorem OAI.Release075.Discrete.Path.integral_form_quadratic (p : Path M a b) (hp : p.Geodesic) {t T : ℕ}
    (ht : t ≤ p.length) (hend : T ≤ M.dist (p.point t) b) :
    ((T/2:ℕ):ℤ)^2 ≤ p.integral (M.form (p.point t) a T) := by sorry
