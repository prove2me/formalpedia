-- Prove2me | Theorems.Thm_OAI_Problem310_FiniteLocalHit_local_test_implies_root_hit
-- name    : OAI.Problem310.FiniteLocalHit.local_test_implies_root_hit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:40:57.841747+00:00
-- url     : https://prove2.me/theorems/72099982-8937-4e15-9927-056ae0c822ae
-- title:
--   A successful child-local test is a terminal hit of the root router
-- statement:
--   **Setting.** Fix $M,d\in\mathbb{N}$. The children of a vertex are labelled $0,1,\dots,M$: child $M$ is the *default* child, and $0,\dots,M-1$ are the *nondefault* children, ordered as integers. A *node* is a finite sequence $P$ of children (the path from the root) of length $|P|<d$, and a *leaf* is a sequence of children of length exactly $d$; $P\frown j$ denotes $P$ followed by the child $j$. Bits are written $0$ (false) and $1$ (true). For $\beta\in\mathbb{N}$ and $y\in\mathbb{R}$ let
--
--   $$\kappa_\beta(y)=\big\lfloor 2^{\beta+2}\,(y-\lfloor y\rfloor)\big\rfloor\in\{0,1,\dots,2^{\beta+2}-1\}$$
--
--   be the index of the cell containing $y$ in the $1$-periodic grid of mesh $2^{-\beta-2}$.
--
--   Let $b_S(P,j)\in\mathbb{N}$ be a resolution for every node $P$ and nondefault child $j$, and $b_T(L)\in\mathbb{N}$ one for every leaf $L$. A *selector table* $\omega_S$ assigns a bit $\omega_S(P,j,m)$ to every node $P$, nondefault child $j$ and cell index $m<2^{b_S(P,j)+2}$; a *terminal table* $\omega_T$ assigns a bit $\omega_T(L,m)$ to every leaf $L$ and $m<2^{b_T(L)+2}$. The selector value of $j$ at a sequence $P$ and a point $y\in\mathbb{R}$ is $\sigma(P,j,y)=\omega_S\big(P,j,\kappa_{b_S(P,j)}(y)\big)$ if $|P|<d$, and $\sigma(P,j,y)=0$ otherwise. The *first-success choice* $c(P,y)$ is the smallest nondefault $j$ with $\sigma(P,j,y)=1$, and the default child $M$ if there is none. Routing appends the chosen child repeatedly: $\rho_0(P,y)=P$ and $\rho_{n+1}(P,y)=\rho_n(P,y)\frown c(\rho_n(P,y),y)$; write $\rho_n(y)=\rho_n(\varnothing,y)$ for the route from the root, so that $\rho_d(y)$ is the leaf reached by the router at $y$.
--
--   **Theorem.** Let $k,r\in\mathbb{N}$, let $U$ be a node, $i\in\{0,\dots,M-1\}$ a nondefault child and $x,y\in\mathbb{R}$, with $|U|+1+r=d$. Assume:
--
--   1. $\rho_k(x)=U$, and $c(\rho_l(x),x)\neq M$ for every $l<k$ (the route of $x$ reaches $U$ without taking a default child);
--   2. for every $l<k$ and every nondefault child $j\le c(\rho_l(x),x)$ one has $\sigma(\rho_l(x),j,x)=\sigma(\rho_l(x),j,y)$ (along the route of $x$, the selectors up to and including the chosen one take the same values at $y$);
--   3. $c(U,x)=M$ (the route of $x$ takes the default child at $U$);
--   4. $\sigma(U,j,x)=\sigma(U,j,y)$ for every nondefault $j<i$;
--   5. the local test of child $i$ succeeds at $y$: $\omega_S\big(U,i,\kappa_{b_S(U,i)}(y)\big)=1$ and $\omega_T\big(L',\kappa_{b_T(L')}(y)\big)=1$, where $L'=\rho_r(U\frown i,\,y)$ is the leaf reached by routing at $y$ from the child $U\frown i$.
--
--   Then the terminal lookup of the root router at $y$ succeeds:
--
--   $$\omega_T\big(\rho_d(y),\ \kappa_{b_T(\rho_d(y))}(y)\big)=1.$$
--
--   In the random construction of the avoiding set, a point $y$ belongs to the random set exactly when the terminal lookup of the root router at $y$ succeeds. The lemma converts a success of a *child-local* test, which only involves the selector of child $i$ at $U$ and the subtree below $U\frown i$, into membership of $y$ in that set. Its only inputs relating $y$ to the center $x$ are equalities of finitely many selector values; later siblings of $i$ at $U$ and all choices off the route of $x$ are unrestricted.
--
--   **Formalization Note** Children are `Fin (M + 1)`: a nondefault child $j$ is `j.castSucc` and the default is `Fin.last M`. The selector value $\sigma$ is `selectorValue bS ωS`, defined on all lists and equal to `false` on lists of length at least $d$; the choice rule is `select (selectorValue bS ωS)` (i.e. `chooseChild` applied to the selector values), routes are `routeFrom`, and `localLeaf` packages a route of the right length as a leaf in `List.Vector (Fin (M + 1)) d`, carrying the depth proof `hdepth`. Table cells are addressed by `selectorAddress` and `terminalAddress` as dependent pairs (table name, cell index).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FiniteLocalHit.lean#L14-L58

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
open FiniteTableModel StableRouting RoutingPath OrderedRouting FiniteLocalPredicate
variable {M d : ℕ}

theorem OAI.Problem310.FiniteLocalHit.local_test_implies_root_hit
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (k r : ℕ) (U : Node M d) (i : Fin M) (x y : ℝ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    (hU : routeFrom (select (selectorValue bS ωS)) k [] x = U.val)
    (hnd : ∀ l < k, select (selectorValue bS ωS)
      (routeFrom (select (selectorValue bS ωS)) l [] x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ select (selectorValue bS ωS)
        (routeFrom (select (selectorValue bS ωS)) l [] x) x →
      selectorValue bS ωS (routeFrom (select (selectorValue bS ωS)) l [] x) j x =
      selectorValue bS ωS (routeFrom (select (selectorValue bS ωS)) l [] x) j y)
    (hdefault : select (selectorValue bS ωS) U.val x = Fin.last M)
    (hearlier : ∀ j < i, selectorValue bS ωS U.val j x = selectorValue bS ωS U.val j y)
    (hlocal : (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT
        (localLeaf (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) hdepth y) y)) = true) :
    ωT (terminalAddress bT
      (localLeaf (select (selectorValue bS ωS)) d [] (by simp) y) y) = true := by sorry
