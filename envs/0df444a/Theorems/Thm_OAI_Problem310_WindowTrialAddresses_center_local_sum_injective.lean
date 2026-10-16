-- Prove2me | Theorems.Thm_OAI_Problem310_WindowTrialAddresses_center_local_sum_injective
-- name    : OAI.Problem310.WindowTrialAddresses.center_local_sum_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:44:20.383434+00:00
-- url     : https://prove2.me/theorems/80aa2601-2737-4b84-84b0-30604273f5da
-- title:
--   Center selector addresses and local trial addresses are pairwise distinct
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
--   *Addresses.* The selector table of a node $Q$ and a nondefault child $j$ has resolution $b(Q\frown j)$; its cells are addressed by the pairs $((Q,j),m)$ with $m<2^{b(Q\frown j)+2}$. The terminal table of a leaf $L$ has resolution $b(L)$; its cells are addressed by the pairs $(L,m)$ with $m<2^{b(L)+2}$. Addresses of different tables are different even when their cell indices coincide. For $x\in\mathbb{R}$ the *center address* of the selector table $(Q,j)$ is $\alpha_x(Q,j)=\big((Q,j),\kappa_{b(Q\frown j)}(x)\big)$.
--
--   *Local trials.* Fix a node $P$. A local trial at $P$ is a pair $z=(i,j)$ with $0\le i<M$ and $0\le j<r_P$; its scale index $n(z)=a(P\frown i)+j$ runs through the window of the child edge $P\frown i$. For $t\in\mathbb{R}$ the trial reads the selector table $(P,i)$ at the shifted point $x+t\,2^{-n(z)}$, i.e. at the address $\beta_{x,t}(z)=\big((P,i),\kappa_{b(P\frown i)}(x+t\,2^{-n(z)})\big)$.
--
--   **Theorem.** Let $W$ be a window datum, $P$ a node, $x\in\mathbb{R}$ and $t\in[1,2]$. Then the combined address map on the disjoint union of all pairs $(Q,j)$ (a node and a nondefault child) and all local trials at $P$,
--
--   $$\alpha_x\sqcup\beta_{x,t}:\ \big\{(Q,j)\big\}\ \sqcup\ \big(\{0,\dots,M-1\}\times\{0,\dots,r_P-1\}\big)\longrightarrow\{\text{selector addresses}\},$$
--
--   is injective. Equivalently: the center addresses of all selector tables are pairwise distinct, the trial addresses at $P$ are pairwise distinct, and no trial address equals any center address (including the center address of the table that the trial itself reads).
--
--   This is the freshness condition for the exact fixed-scale computation: when all selector entries are independent fair bits, conditioning on the complete center exposure (the bits at all addresses $\alpha_x(Q,j)$) leaves the bits read by the local trials at $P$ independent and fair.
--
--   **Formalization Note** The statement is `Function.Injective (Sum.elim (fun e => selectorAddress (selectorEndpoints W) e.1 e.2 x) (localSelectorAddress W P x t))` on `(Node M d × Fin M) ⊕ LocalTrial W P`, where `LocalTrial W P = Fin M × Fin (W.r (d - P.val.length))` and the scale index is `localIndex W P`. The selector resolution of $(Q,j)$ is `selectorEndpoints W Q j = W.b (Q.val ++ [j.castSucc])`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowTrialAddresses.lean#L65-L85

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses

open OAI OAI.Problem310 OAI.Problem310.WindowTrialAddresses
open FiniteTableModel TrialAddresses
variable {M d g r₀ : ℕ}

theorem OAI.Problem310.WindowTrialAddresses.center_local_sum_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Function.Injective (Sum.elim
      (fun e : Node M d × Fin M => selectorAddress (selectorEndpoints W) e.1 e.2 x)
      (localSelectorAddress W P x t)) := by sorry
