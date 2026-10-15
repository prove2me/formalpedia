-- Prove2me | Theorems.Thm_OAI_ForestSpace_Diamond_Network_refine_connected
-- name    : OAI.ForestSpace.Diamond.Network.refine_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:29:56.344424+00:00
-- url     : https://prove2.me/theorems/f0a9a3e6-7e10-43dc-9c75-28e8a94b009f
-- title:
--   Replacing every edge by countably many two-edge paths preserves connectedness
-- statement:
--   A *network* $A$ consists of a vertex set $V(A)$, an edge set $\mathcal E(A)$ (both arbitrary, possibly infinite sets) and, for every edge $e$, two distinct endpoints $l(e)\ne r(e)$ in $V(A)$. Its graph $G(A)$ is the simple graph on $V(A)$ in which $u$ and $v$ are adjacent if and only if they are the two endpoints of some edge (in either order).
--
--   The *refinement* $A'$ replaces every edge by countably many internally disjoint paths of length two. Its vertex set is $V(A)\sqcup(\mathcal E(A)\times\mathbb{N})$, consisting of the old vertices and new midpoints $m_{e,j}$, and for every edge $e$ and every $j\in\mathbb{N}$ it has one edge from $l(e)$ to $m_{e,j}$ and one edge from $m_{e,j}$ to $r(e)$. The theorem states:
--
--   $$
--   G(A)\ \text{is connected}\ \Longrightarrow\ G(A')\ \text{is connected},
--   $$
--
--   where a graph is connected if it is nonempty and any two of its vertices are joined by a walk.
--
--   Iterating the refinement from a single edge produces the countably branching diamond graphs $D_k$. Connectedness of all iterates is what makes their graph distances genuine shortest-path distances, and it is used to show that each refinement doubles the distances between old vertices.
--
--   **Formalization Note** `Network` has fields `V`, `E`, `left`, `right`, `distinct`; `A.graph : SimpleGraph A.V`. In `A.refine` the vertex type is `A.V ⊕ (A.E × ℕ)` and the edge type is `A.E × ℕ × Bool`, the edge `(e, j, false)` joining `left e` to `(e, j)` and `(e, j, true)` joining `(e, j)` to `right e`. Connectedness is Mathlib's `SimpleGraph.Connected` (preconnected and nonempty).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Diamonds.lean#L91-L110

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

open OAI OAI.ForestSpace OAI.ForestSpace.Diamond OAI.ForestSpace.Diamond.Network
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable (A : Network)

theorem OAI.ForestSpace.Diamond.Network.refine_connected (hA : A.graph.Connected) : A.refine.graph.Connected := by sorry
