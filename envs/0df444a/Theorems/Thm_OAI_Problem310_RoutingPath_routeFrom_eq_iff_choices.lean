-- Prove2me | Theorems.Thm_OAI_Problem310_RoutingPath_routeFrom_eq_iff_choices
-- name    : OAI.Problem310.RoutingPath.routeFrom_eq_iff_choices
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:13:53.976351+00:00
-- url     : https://prove2.me/theorems/2cf6b975-c433-46af-b518-7cca6d294426
-- title:
--   A route equals a given word iff each decision along the word agrees with it
-- statement:
--   Let $\iota$ be a set of child labels and $X$ a set of parameters. A *decision rule* is a map $\operatorname{ch}$ that assigns to every finite word $P$ over $\iota$ (a node of the infinite $\iota$-ary tree, the empty word $\varnothing$ being the root) and every parameter $x\in X$ a child $\operatorname{ch}(P,x)\in\iota$. The route of $x$ from a node $P$ is obtained by repeatedly appending the chosen child:
--   $$R_0(P,x)=P,\qquad R_{k+1}(P,x)=R_k(P,x)\,\operatorname{ch}\bigl(R_k(P,x),x\bigr).$$
--
--   Let $L=(L_0,\dots,L_{\ell-1})$ be a word of length $\ell$ over $\iota$ and $x\in X$, and for $k\le\ell$ write $L_{<k}=(L_0,\dots,L_{k-1})$ for its prefix of length $k$. Then the route of $x$ from the root equals $L$ after $\ell$ steps exactly when every decision along $L$ agrees with $L$:
--   $$R_\ell(\varnothing,x)=L\iff \operatorname{ch}(L_{<k},x)=L_k\ \text{ for all } 0\le k<\ell .$$
--
--   This is the path-cylinder description of routing: the event that a prescribed word is reached is the intersection of $\ell$ node-decision events, each involving the decision rule at a single prefix of $L$. When the decision rule is random, this turns the probability of following a fixed path into a statement about the decisions at the nodes of that path only.
--
--   **Formalization Note** The route is `routeFrom choose n P x`; words are Lean lists, the root is the empty list, and the prefix $L_{<k}$ is `L.take k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean#L123-L138

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath

open OAI OAI.Problem310 OAI.Problem310.RoutingPath
universe u_ι u_X
variable {ι : Type u_ι} {X : Type u_X}

theorem OAI.Problem310.RoutingPath.routeFrom_eq_iff_choices (choose : List ι → X → ι) (L : List ι) (x : X) :
    routeFrom choose L.length [] x = L ↔
      ∀ (k : ℕ) (hk : k < L.length), choose (L.take k) x = L[k] := by sorry
