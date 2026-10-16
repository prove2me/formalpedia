-- Prove2me | Theorems.Thm_OAI_Problem310_WindowTrialAddresses_window_fixed_scale_on_center_atom
-- name    : OAI.Problem310.WindowTrialAddresses.window_fixed_scale_on_center_atom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:52:08.953863+00:00
-- url     : https://prove2.me/theorems/e70011eb-68d8-4d23-a97f-9ddb88b62682
-- title:
--   Exact fixed-scale failure mass on a center-exposure atom for the window-indexed table model
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
--   *Random tables.* A selector outcome $a$ assigns a bit to every selector address and a terminal outcome $\tau$ a bit to every terminal address. Let $\mu_S$ make all selector bits independent fair bits; for $p\in[0,1]$ let $\mu_T^p$ make all terminal bits independent, each equal to $1$ with probability $p$; and let $\mathbb{P}_p=\mu_S\otimes\mu_T^p$ be the joint law, with selector and terminal tables independent.
--
--   **Theorem.** Let $W$ be a window datum, $P$ a node, $x\in\mathbb{R}$, $t\in[1,2]$, $p\in[0,1]$, and let $v$ assign a bit $v(Q,j)$ to every node $Q$ and nondefault child $j$. Let $\lambda$ assign to every selector outcome $a$ and every local trial $z=(i,j)$ at $P$ a leaf $\lambda(a,z)$ such that $P\frown i$ is a prefix of $\lambda(a,z)$. Consider the event $F$ that the center exposure equals $v$ and that every active trial reads a failing terminal bit:
--
--   $$F=\Big\{(a,\tau):\ a(\alpha_x(Q,j))=v(Q,j)\ \text{for all }(Q,j),\ \text{and}\ \tau\Big(\lambda(a,z),\,\kappa_{b(\lambda(a,z))}\big(x+t\,2^{-n(z)}\big)\Big)=0\ \text{for every trial } z \text{ with } a(\beta_{x,t}(z))=1\Big\}.$$
--
--   Then
--
--   $$\mathbb{P}_p(F)=\mu_S\big(\{a:\ a(\alpha_x(Q,j))=v(Q,j)\ \text{for all }(Q,j)\}\big)\cdot\Big(1-\frac p2\Big)^{M\,r_P}.$$
--
--   In the application $\lambda(a,z)$ is the leaf reached by routing from the child $P\frown i$ at the trial point, so it depends on the selector outcome. Nevertheless, conditionally on the exposure atom the $M\,r_P$ local trials are independently active with probability $\tfrac12$, and an active trial fails with probability $1-p$. All address-injectivity requirements are discharged by the window axioms; the only condition on the leaves is that each stays below the child it tests.
--
--   **Formalization Note** The laws are `outcomeLaw`, `selectorLaw` and `terminalLaw`, built as product measures from `fairLaw` and `bitLaw p hp0 hp1` (Mathlib's `bernoulliMeasure`, giving `true` probability $p$) on the finite function spaces `SelectorTable (selectorEndpoints W)` and `TerminalTable (terminalEndpoints W)`. Local trials are `LocalTrial W P = Fin M × Fin (W.r (d - P.val.length))`, $n(z)$ is `localIndex W P z` and $\beta_{x,t}$ is `localSelectorAddress W P x t`. Measures take values in $[0,\infty]$ and the factor $1-p/2$ is `ENNReal.ofReal (1 - p / 2)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowFixedScale.lean#L17-L50

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
open MeasureTheory
open FiniteTableModel ConcreteLabels
variable {M d g r₀ : ℕ}

theorem OAI.Problem310.WindowTrialAddresses.window_fixed_scale_on_center_atom
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (x t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (value : Node M d × Fin M → Bool)
    (leaf : SelectorTable (selectorEndpoints W) → LocalTrial W P → Leaf M d)
    (hprefix : ∀ a z, (selectorEdge P z.1).IsPrefix (leaf a z).val) :
    outcomeLaw (SelectorAddress (selectorEndpoints W)) (TerminalAddress (terminalEndpoints W))
      p hp0 hp1
      {z : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W) |
        (∀ c : Node M d × Fin M,
          z.1 (selectorAddress (selectorEndpoints W) c.1 c.2 x) = value c) ∧
        ∀ i : LocalTrial W P, z.1 (localSelectorAddress W P x t i) = true →
          z.2 (terminalAddress (terminalEndpoints W) (leaf z.1 i)
            (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P i))) = false} =
      selectorLaw (SelectorAddress (selectorEndpoints W))
        {a | ∀ c : Node M d × Fin M,
          a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = value c} *
      (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - P.val.length)) := by sorry
