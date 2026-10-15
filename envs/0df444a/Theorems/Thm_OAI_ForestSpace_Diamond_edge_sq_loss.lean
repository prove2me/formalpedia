-- Prove2me | Theorems.Thm_OAI_ForestSpace_Diamond_edge_sq_loss
-- name    : OAI.ForestSpace.Diamond.edge_sq_loss
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:30:41.058004+00:00
-- url     : https://prove2.me/theorems/19437a0a-756d-4633-82de-a91ff7f86bac
-- title:
--   Squared distortion loss along original edges of iterated network refinements in spaces with the lens property
-- statement:
--   Let $E$ be a real normed space with the *lens property*: for all $R>0$, $\varepsilon>0$, $x\in E$ and every sequence $(y_j)_{j\in\mathbb{N}}$ in $E$ with $\|x+y_j\|\le R$ and $\|x-y_j\|\le R$ for all $j$ and $\|y_i-y_j\|\ge\varepsilon$ for all $i\ne j$, one has $\varepsilon^2/48\le R^2-\|x\|^2$.
--
--   A *network* $A$ consists of a vertex set $V(A)$, an edge set $\mathcal E(A)$ (arbitrary sets) and distinct endpoints $l(e)\ne r(e)$ for every edge $e$; $G(A)$ is the simple graph on $V(A)$ in which $u,v$ are adjacent if and only if they are the endpoints of some edge. The refinement $A'$ keeps all old vertices and replaces every edge $e$ by countably many internally disjoint two-edge paths $l(e),m_{e,j},r(e)$ ($j\in\mathbb{N}$) through new midpoints $m_{e,j}$. Define the iterates $A^{(0)}=A$ and $A^{(n+1)}=(A')^{(n)}$, write $d_n$ for the shortest-path distance of $G(A^{(n)})$, and let $\iota_n:V(A)\to V(A^{(n)})$ be the canonical inclusion of the original vertices.
--
--   Assume that $G(A)$ is connected. Let $n\in\mathbb{N}$, $C\ge0$, and let $f:V(A^{(n)})\to E$ satisfy $d_n(u,v)\le\|f(u)-f(v)\|\le C\,d_n(u,v)$ for all vertices $u,v$ of $A^{(n)}$. Then for every edge $e$ of $A$,
--
--   $$
--   \left(\frac{\|f(\iota_n(r(e)))-f(\iota_n(l(e)))\|}{2^n}\right)^2+\frac{n}{12}\ \le\ C^2 .
--   $$
--
--   Since the endpoints of $e$ are at distance $2^n$ in $A^{(n)}$, the first term is at least $1$, so the bound forces $C\ge\sqrt{1+n/12}$. Applied to the single-edge network, whose iterates are the countably branching diamond graphs $D_k$, this gives the distortion lower bound $\sqrt{1+k/12}$ for diamonds in any space with the lens property, in particular in $J(T)^*$. The estimate is stated edge by edge, so no supremum of edge stretches needs to be attained.
--
--   **Formalization Note** The lens property is `LensProperty E`; the iterates and inclusions are `A.iterate n` and `A.old n`, and $d_n$ is Mathlib's `SimpleGraph.dist` cast to $\mathbb{R}$ (which would be $0$ for unreachable pairs; here all iterates are connected).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Distortion.lean#L67-L136

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
import Definitions.Def_OAI_Analysis_ForestSpace_Components
import Definitions.Def_OAI_Analysis_ForestSpace_FullDual
import Definitions.Def_OAI_Analysis_ForestSpace_Diamonds
import Definitions.Def_OAI_Analysis_ForestSpace_Distortion

open OAI OAI.ForestSpace OAI.ForestSpace.Diamond
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.ForestSpace.Diamond.edge_sq_loss (hLens : LensProperty E) (A : Network) (hA : A.graph.Connected)
    (n : ℕ) (f : (A.iterate n).V → E) (C : ℝ) (hC : 0 ≤ C)
    (hl : ∀ u v, ((A.iterate n).graph.dist u v : ℝ) ≤ ‖f u-f v‖)
    (hu : ∀ u v, ‖f u-f v‖ ≤ C*((A.iterate n).graph.dist u v : ℝ))
    (e : A.E) :
    (‖f (A.old n (A.right e))-f (A.old n (A.left e))‖/(2:ℝ)^n)^2+(n:ℝ)/12 ≤ C^2 := by sorry
