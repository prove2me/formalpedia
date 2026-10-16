-- Prove2me | Theorems.Thm_OAI_Problem310_WindowLocalHit_ancestor_selector_gap
-- name    : OAI.Problem310.WindowLocalHit.ancestor_selector_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:40:12.811977+00:00
-- url     : https://prove2.me/theorems/50b9f0b8-5cec-49a0-a151-d210efeb5c58
-- title:
--   Windows of selectors tested earlier on a route end before every later edge window begins
-- statement:
--   *Window data.* Let $q,d,g,r_0\in\mathbb{N}$. Words over the alphabet $\{0,\dots,q-1\}$ are the vertices of the complete $q$-ary tree; $|P|$ is the length of a word $P$, $Pi$ is $P$ followed by the letter $i$, and $P\sqsubseteq Q$ means that $P$ is a prefix of $Q$. A word $P$ is a *valid edge* if $P\neq\varnothing$ and $|P|\le d$ (it names the edge entering the vertex $P$). A *window datum* $W$ with parameters $(q,d,g,r_0)$ consists of a function $r_W:\mathbb{N}\to\mathbb{N}$ and maps $a,b,b^*$ from words to $\mathbb{N}$ such that, writing $\ell(P)=r_W(d+1-|P|)$ and letting $P,Q$ range over valid edges:
--
--   1. $1\le\ell(P)$, $r_0\le\ell(P)$ and $a(P)\ge3$;
--   2. $b(P)+1=a(P)+\ell(P)$, so the edge $P$ carries the window of dyadic scales $a(P),\dots,b(P)$;
--   3. (prefix gap) if $P\sqsubseteq Q$ and $P\neq Q$, then $b(P)+g<a(Q)$;
--   4. (sibling gap) for every word $V$, letters $i<j$ and word $T$ such that $Vi$ and $VjT$ are valid edges, $b(Vi)+g<a(VjT)$;
--   5. (descendant bounds) if $P\sqsubseteq Q$, then $b(P)\le b(Q)\le b^*(P)$;
--   6. (padding) $b^*(P)+1\le a(P)+2\ell(P)$.
--
--   *Routing.* Let $X$ be any set and let $\chi$ be any child-choice map assigning a letter $\chi(P,x)\in\{0,\dots,q-1\}$ to every word $P$ and every $x\in X$. For $x\in X$ the route from the root is $\rho_0(x)=\varnothing$ and $\rho_{n+1}(x)=\rho_n(x)\,c_n(x)$, where $c_n(x)=\chi(\rho_n(x),x)$ is the child chosen at stage $n$.
--
--   **Theorem.** Let $W$ be a window datum with parameters $(q,d,g,r_0)$, let $x\in X$, let $k<l<d$, and let $i,j\in\{0,\dots,q-1\}$ with $j\le c_k(x)$. Then
--
--   $$b\bigl(\rho_k(x)\,j\bigr)+g<a\bigl(\rho_l(x)\,i\bigr).$$
--
--   Under first-success routing, the selectors examined at the stage-$k$ node $\rho_k(x)$ are those of the children $j\le c_k(x)$: the rejected ones and the chosen one. The theorem says that the window of every such edge ends more than $g$ scales before the window of any edge leaving a later node $\rho_l(x)$ of the same route begins. It is a purely deterministic consequence of the prefix-gap and sibling-gap axioms, and it is used to separate the ranges of scales involved at different stages of a route.
--
--   **Formalization Note** The window datum is `W : WindowData q d g r₀` (all axioms listed above are part of the structure, though only the two gap axioms are used here); the choice map is `choose : List (Fin q) → X → Fin q`, the route is `routeFrom choose n [] x`, and letters are compared in `Fin q`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowLocalHit.lean#L18-L54

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge

open OAI OAI.Problem310
universe u_X
open RoutingPath StableRouting GridSeparation
variable {q d g r₀ : ℕ} {X : Type u_X}

theorem OAI.Problem310.WindowLocalHit.ancestor_selector_gap (W : WindowData q d g r₀)
    (choose : List (Fin q) → X → Fin q) (x : X)
    {k l : ℕ} (hkl : k < l) (hld : l < d) (i j : Fin q)
    (hj : j ≤ choose (routeFrom choose k [] x) x) :
    W.b (routeFrom choose k [] x ++ [j]) + g <
      W.a (routeFrom choose l [] x ++ [i]) := by sorry
