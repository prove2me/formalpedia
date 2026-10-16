-- Prove2me | Theorems.Thm_OAI_Problem310_WindowExceptionalTransfer_exists_representatives_failure_transfer
-- name    : OAI.Problem310.WindowExceptionalTransfer.exists_representatives_failure_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:41:39.460467+00:00
-- url     : https://prove2.me/theorems/0f00a4d1-4eb1-4bd1-b20a-6e67673c28e4
-- title:
--   On a good exposure atom, exceptional centers fail all local tests at one of finitely many representative scales
-- statement:
--   **Setting.** Fix $M,d\in\mathbb{N}$. The children of a vertex are labelled $0,1,\dots,M$: child $M$ is the *default* child, and $0,\dots,M-1$ are the *nondefault* children, ordered as integers. A *node* is a finite sequence $P$ of children (the path from the root) of length $|P|<d$, and a *leaf* is a sequence of children of length exactly $d$; $P\frown j$ denotes $P$ followed by the child $j$. Bits are written $0$ (false) and $1$ (true). For $\beta\in\mathbb{N}$ and $y\in\mathbb{R}$ let
--
--   $$\kappa_\beta(y)=\big\lfloor 2^{\beta+2}\,(y-\lfloor y\rfloor)\big\rfloor\in\{0,1,\dots,2^{\beta+2}-1\}$$
--
--   be the index of the cell containing $y$ in the $1$-periodic grid of mesh $2^{-\beta-2}$.
--
--   *Window data.* Fix also $g,r_0\in\mathbb{N}$. Call a sequence of children $P\neq\varnothing$ with $|P|\le d$ an *edge* (it stands for the edge into its last vertex). A window datum $W$ consists of maps $r:\mathbb{N}\to\mathbb{N}$ and $a,b,b^*$ from finite sequences of children to $\mathbb{N}$ such that, for all edges $P,Q$:
--
--   - (i) $r(d+1-|P|)\ge 1$ and $r(d+1-|P|)\ge r_0$;
--   - (ii) $a(P)\ge 3$;
--   - (iii) $b(P)+1=a(P)+r(d+1-|P|)$, so the *window* $\{a(P),\dots,b(P)\}$ of $P$ consists of $r(d+1-|P|)$ consecutive scale indices;
--   - (iv) if $P$ is a proper prefix of $Q$, then $b(P)+g<a(Q)$;
--   - (v) if $P=V\frown i$ and $Q=V\frown j\frown V'$ with $i<j$ (for any sequences $V,V'$), then $b(P)+g<a(Q)$;
--   - (vi) if $P$ is a prefix of $Q$, then $b(P)\le b(Q)\le b^*(P)$;
--   - (vii) $b^*(P)+1\le a(P)+2\,r(d+1-|P|)$.
--
--   For a node $U$, all child edges $U\frown i$ have windows of the same length $r_U=r(d-|U|)$.
--
--   *Tables and routing.* The selector table of a node $P$ and a nondefault child $j$ has resolution $b(P\frown j)$, and the terminal table of a leaf $L$ has resolution $b(L)$. A pair of tables $\omega=(\omega_S,\omega_T)$ assigns bits $\omega_S(P,j,m)$ for $m<2^{b(P\frown j)+2}$ and $\omega_T(L,m)$ for $m<2^{b(L)+2}$. For $y\in\mathbb{R}$ let $\sigma(P,j,y)=\omega_S(P,j,\kappa_{b(P\frown j)}(y))$ for nodes $P$ (and $\sigma(P,j,y)=0$ for longer sequences), let the first-success choice $c(P,y)$ be the smallest nondefault $j$ with $\sigma(P,j,y)=1$, or the default $M$ if there is none, and route by $\rho_0(P,y)=P$, $\rho_{n+1}(P,y)=\rho_n(P,y)\frown c(\rho_n(P,y),y)$, $\rho_n(y)=\rho_n(\varnothing,y)$. (These objects depend on $\omega_S$, which is suppressed from the notation.) The *routed set* of $\omega$ is
--
--   $$E(\omega)=\big\{y\in\mathbb{R}:\ \omega_T\big(\rho_d(y),\kappa_{b(\rho_d(y))}(y)\big)=1\big\}.$$
--
--   For a node $U$ and a nondefault child $i$, the *local test* $Q_{U,i}(\omega,y)$ equals $1$ exactly when $\omega_S(U,i,\kappa_{b(U\frown i)}(y))=1$ and $\omega_T(L,\kappa_{b(L)}(y))=1$, where $L=\rho_{d-|U|-1}(U\frown i,y)$ is the leaf reached by routing at $y$ from the child $U\frown i$.
--
--   *Center data.* The *center exposure* of a selector table $\omega_S$ at $x\in\mathbb{R}$ is the vector $\Xi_x(\omega_S)=\big(\omega_S(P,j,\kappa_{b(P\frown j)}(x))\big)_{(P,j)}$ of all selector bits read at $x$, one for every node $P$ and nondefault child $j$. The point $x$ is *stable* if $\sigma(P,j,x)=\sigma(P,j,x+t\,2^{-n})$ for every node $P$, nondefault child $j$, integer $n>b(P\frown j)+g$, scale $t\in[1,2]$ and selector table $\omega_S$. Finally, $x$ is *exceptional* for a set $B\subseteq\mathbb{R}$ if there is $t\in[1,2]$ such that $x+t\,2^{-n}\notin B$ for every integer $n\ge 1$.
--
--   **Theorem.** Let $W$ be a window datum, $U$ a node, $k\in\mathbb{N}$, $x\in\mathbb{R}$, and let $\xi$ assign a bit to every pair $(P,j)$ of a node and a nondefault child. Assume that $x$ is stable and that on the exposure atom $\{\Xi_x=\xi\}$ the route of $x$ takes its first default at $U$ after $k$ steps: for every selector table $\omega_S$ with $\Xi_x(\omega_S)=\xi$,
--
--   $$\rho_k(x)=U,\qquad c(U,x)=M,\qquad c(\rho_l(x),x)\neq M\ \text{ for all } l<k .$$
--
--   Then there is a finite set $R\subseteq[1,2]$ with
--
--   $$|R|\le 1+M\,r_U\,2^{2r_U+2}$$
--
--   such that for every pair of tables $\omega=(\omega_S,\omega_T)$ with $\Xi_x(\omega_S)=\xi$ for which $x$ is exceptional for the routed set $E(\omega)$, some $t\in R$ satisfies
--
--   $$Q_{U,i}\big(\omega,\ x+t\,2^{-(a(U\frown i)+j)}\big)=0\qquad\text{for all } 0\le i<M \text{ and } 0\le j<r_U .$$
--
--   Exceptionality is an existential statement over the continuum of scales $t\in[1,2]$. On a fixed exposure atom on which the route of $x$ first defaults at $U$, the theorem replaces it by the failure of all $M\,r_U$ local tests in the child windows of $U$ at one of finitely many representative scales, and the set $R$ is chosen before the tables. This reduces the probability that $x$ is exceptional to a union bound over $R$ of fixed-scale failure events.
--
--   **Formalization Note** The window datum is `W : WindowData (M + 1) d g r₀` (the first parameter is the total number of children); the selector and terminal resolutions are `selectorEndpoints W` and `terminalEndpoints W`, the choice rule is `selectorChoice`, the routed set is `routedSet`, the local test is `localQ W U ω i`, stability is `StableAt W x` and the exposure is `centerExposure`. Exceptionality is membership in `Auxiliary.exceptionalCenters (routedSet …) (Set.Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)`. The bound on $|R|$ is the cardinality of a `Finset`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowExceptionalTransfer.lean#L72-L116

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer

open OAI OAI.Problem310 OAI.Problem310.WindowExceptionalTransfer
open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate CenterRouteExposure
variable {M d g r₀ : ℕ}

theorem OAI.Problem310.WindowExceptionalTransfer.exists_representatives_failure_transfer
    (W : WindowData (M + 1) d g r₀) (U : Node M d) (k : ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool)
    (hfirst : ∀ ω : SelectorTable (selectorEndpoints W),
      centerExposure (selectorEndpoints W) x ω = ξ →
      routeFrom (selectorChoice (selectorEndpoints W) ω) k [] x = U.val ∧
      selectorChoice (selectorEndpoints W) ω U.val x = Fin.last M ∧
      ∀ l < k, selectorChoice (selectorEndpoints W) ω
        (routeFrom (selectorChoice (selectorEndpoints W) ω) l [] x) x ≠ Fin.last M)
    (hstable : StableAt W x) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W),
        centerExposure (selectorEndpoints W) x ω.1 = ξ →
        x ∈ Auxiliary.exceptionalCenters
          (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
          (Set.Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n) →
        ∃ t ∈ R, ∀ (i : Fin M) (j : Fin (W.r (d - U.val.length))),
          localQ W U ω i
            (x + t * (2 : ℝ)⁻¹ ^ (W.a (U.val ++ [i.castSucc]) + j.val)) = false := by sorry
