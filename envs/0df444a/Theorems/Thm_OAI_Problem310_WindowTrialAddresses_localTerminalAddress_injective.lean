-- Prove2me | Theorems.Thm_OAI_Problem310_WindowTrialAddresses_localTerminalAddress_injective
-- name    : OAI.Problem310.WindowTrialAddresses.localTerminalAddress_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:45:45.121217+00:00
-- url     : https://prove2.me/theorems/37e3b038-6bba-41af-a34c-e27bef74348b
-- title:
--   Local trials read distinct terminal cells when their leaves stay below the tested child
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
--   **Theorem.** Let $W$ be a window datum, $P$ a node, $x\in\mathbb{R}$ and $t\in[1,2]$. Let $\lambda$ assign to every local trial $z=(i,j)$ at $P$ a leaf $\lambda(z)$ such that the child edge $P\frown i$ is a prefix of $\lambda(z)$. Then the terminal addresses read by the trials,
--
--   $$z\longmapsto\Big(\lambda(z),\ \kappa_{b(\lambda(z))}\big(x+t\,2^{-n(z)}\big)\Big),$$
--
--   are pairwise distinct, i.e. this map on $\{0,\dots,M-1\}\times\{0,\dots,r_P-1\}$ is injective.
--
--   No numerical hypothesis is needed beyond the window axioms: they force the terminal resolution of every leaf below $P\frown i$ to refine the resolution $b(P\frown i)$ of the child window. In the random model the leaf $\lambda(z)$ is reached by routing from $P\frown i$ and depends on the selector tables; applying the theorem for each selector outcome shows that distinct trials always read distinct terminal cells, so their terminal bits are independent.
--
--   **Formalization Note** Leaves are `Leaf M d = List.Vector (Fin (M + 1)) d`, the prefix condition is `(selectorEdge P z.1).IsPrefix (leaf z).val` with `selectorEdge P i = P.val ++ [i.castSucc]`, the terminal resolution is `terminalEndpoints W L = W.b L.val`, and the address is `terminalAddress (terminalEndpoints W) (leaf z) (x + t * (2 : ℝ)⁻¹ ^ localIndex W P z)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowTrialAddresses.lean#L87-L113

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

theorem OAI.Problem310.WindowTrialAddresses.localTerminalAddress_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (leaf : LocalTrial W P → Leaf M d)
    (hprefix : ∀ z, (selectorEdge P z.1).IsPrefix (leaf z).val) :
    Function.Injective (fun z : LocalTrial W P =>
      terminalAddress (terminalEndpoints W) (leaf z)
        (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P z))) := by sorry
