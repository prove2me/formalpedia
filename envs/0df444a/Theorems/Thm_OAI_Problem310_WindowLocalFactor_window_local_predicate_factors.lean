-- Prove2me | Theorems.Thm_OAI_Problem310_WindowLocalFactor_window_local_predicate_factors
-- name    : OAI.Problem310.WindowLocalFactor.window_local_predicate_factors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:38:54.278603+00:00
-- url     : https://prove2.me/theorems/87cce83d-b293-4dbf-9572-20c25ddaa4eb
-- title:
--   Window data supply a common dyadic grid for the local test below a child edge
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
--   *Finite table model.* Take $q=M+1$, so that the letter $M$ is the default child and $0,\dots,M-1$ are the nondefault children; a *node* is a word of length $<d$ and a *leaf* is a word of length $d$. Use the window endpoints as resolutions: $b_S(Q,j)=b(Qj)$ for nodes $Q$ and $j<M$, and $b_T(L)=b(L)$ for leaves $L$. With $\kappa_\beta(y)=\lfloor 2^{\beta+2}\{y\}\rfloor$, where $\{y\}=y-\lfloor y\rfloor$, a selector table $\omega_S$ has bits $\omega_S(Q,j,c)$ for $c<2^{b_S(Q,j)+2}$, a terminal table $\omega_T$ has bits $\omega_T(L,c)$ for $c<2^{b_T(L)+2}$, and the selector bit of $(Q,j)$ at $y\in\mathbb{R}$ is $\sigma^{\omega_S}_{Q,j}(y)=\omega_S(Q,j,\kappa_{b_S(Q,j)}(y))$ if $|Q|<d$, and $\mathrm{false}$ otherwise. Let $\chi(Q,y)=R_Q\bigl(\sigma^{\omega_S}_{Q,0}(y),\dots,\sigma^{\omega_S}_{Q,M-1}(y)\bigr)\in\{0,\dots,M\}$ for arbitrary rules $R_Q:\{\mathrm{true},\mathrm{false}\}^M\to\{0,\dots,M\}$, and let $\rho_m(P,y)$ be the word obtained from $P$ by $m$ successive steps of appending the chosen child $\chi(\cdot,y)$.
--
--   **Theorem.** Let $W$ be a window datum with parameters $(M+1,d,g,r_0)$, let $\omega_S,\omega_T$ be tables as above, let $U$ be a node, $i<M$, and $m\in\mathbb{N}$ with $|U|+1+m=d$. Put $P=Ui$ and let $\lambda(y)=\rho_m(P,y)$, a leaf. If $x,y\in\mathbb{R}$ satisfy $\lfloor 2^{b^*(P)+2}\{x\}\rfloor=\lfloor 2^{b^*(P)+2}\{y\}\rfloor$, then
--
--   $$\omega_S\bigl(U,i,\kappa_{b(P)}(x)\bigr)\wedge\omega_T\bigl(\lambda(x),\kappa_{b(\lambda(x))}(x)\bigr)=\omega_S\bigl(U,i,\kappa_{b(P)}(y)\bigr)\wedge\omega_T\bigl(\lambda(y),\kappa_{b(\lambda(y))}(y)\bigr).$$
--
--   So the local test "the selector of the edge $Ui$ succeeds and the terminal bit at the leaf reached below it is $\mathrm{true}$" is constant on the cells of the periodic dyadic grid of mesh $2^{-(b^*(Ui)+2)}$, for every choice of the tables. The window datum thus identifies $b^*(Ui)$ as the resolution at which scale representatives for this test can be chosen, with no further hypotheses on the resolutions.
--
--   **Formalization Note** The window datum is `W : WindowData (M + 1) d g r₀`, with fields `r`, `a`, `b`, `bstar` and axioms `length_pos`, `length_threshold`, `start_three`, `endpoint`, `gap_prefix`, `gap_sibling`, `descendant_bounds`, `padding` as listed above. In the Lean statement the resolutions `bS`, `bT` are arbitrary functions tied to $W$ by the hypotheses `hbS`, `hbT`; the choice map is `choose`, linked to `rule` by `hchoose`; the letter $i$ enters words as `i.castSucc`; the depth $m$ is the variable `r`; and $\lambda(y)$ is `FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth y`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowLocalFactor.lean#L73-L121

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

open OAI OAI.Problem310
universe u_Ω
open RoutingPath GridSeparation

theorem OAI.Problem310.WindowLocalFactor.window_local_predicate_factors {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀)
    (bS : FiniteTableModel.Node M d → Fin M → ℕ)
    (bT : FiniteTableModel.Leaf M d → ℕ)
    (hbS : ∀ Q j, bS Q j = W.b (Q.val ++ [j.castSucc]))
    (hbT : ∀ L, bT L = W.b L.val)
    (ωS : FiniteTableModel.SelectorTable bS) (ωT : FiniteTableModel.TerminalTable bT)
    (choose : List (FiniteTableModel.Child M) → ℝ → FiniteTableModel.Child M)
    (rule : List (FiniteTableModel.Child M) → (Fin M → Bool) → FiniteTableModel.Child M)
    (hchoose : ∀ Q x, choose Q x = rule Q (fun j => FiniteTableModel.selectorValue bS ωS Q j x))
    (U : FiniteTableModel.Node M d) (i : Fin M) (r : ℕ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract y⌋) :
    (ωS (FiniteTableModel.selectorAddress bS U i x) &&
      ωT (FiniteTableModel.terminalAddress bT
        (FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth x) x)) =
    (ωS (FiniteTableModel.selectorAddress bS U i y) &&
      ωT (FiniteTableModel.terminalAddress bT
        (FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth y) y)) := by sorry
