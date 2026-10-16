-- Prove2me | Theorems.Thm_OAI_Problem310_WindowLocalFactor_exists_concrete_local_representatives
-- name    : OAI.Problem310.WindowLocalFactor.exists_concrete_local_representatives
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:39:30.390975+00:00
-- url     : https://prove2.me/theorems/d6845a0c-a032-4f7b-be05-cd15d50ff5e1
-- title:
--   Scale representatives for the concrete selector-and-terminal tests below a node
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
--   *Finite table model.* Take $q=M+1$, so that the letter $M$ is the default child and $0,\dots,M-1$ are the nondefault children; a *node* is a word of length $<d$ and a *leaf* is a word of length $d$. Use the window endpoints as resolutions: $b_S(Q,j)=b(Qj)$ for nodes $Q$ and $j<M$, and $b_T(L)=b(L)$ for leaves $L$. With $\kappa_\beta(y)=\lfloor 2^{\beta+2}\{y\}\rfloor$, where $\{y\}=y-\lfloor y\rfloor$, a selector table $\omega_S$ has bits $\omega_S(Q,j,c)$ for $c<2^{b_S(Q,j)+2}$, a terminal table $\omega_T$ has bits $\omega_T(L,c)$ for $c<2^{b_T(L)+2}$, and the selector bit of $(Q,j)$ at $y\in\mathbb{R}$ is $\sigma^{\omega_S}_{Q,j}(y)=\omega_S(Q,j,\kappa_{b_S(Q,j)}(y))$ if $|Q|<d$, and $\mathrm{false}$ otherwise. For every selector table $\omega_S$ let the child-choice map be $\chi_{\omega_S}(Q,y)=R_Q\bigl(\sigma^{\omega_S}_{Q,0}(y),\dots,\sigma^{\omega_S}_{Q,M-1}(y)\bigr)$ for fixed but arbitrary rules $R_Q:\{\mathrm{true},\mathrm{false}\}^M\to\{0,\dots,M\}$, and let $\rho^{\omega_S}_m(P,y)$ be the word obtained from $P$ by $m$ successive steps of appending $\chi_{\omega_S}(\cdot,y)$.
--
--   Let $W$ be a window datum with parameters $(M+1,d,g,r_0)$. Fix a node $U$, a point $x\in\mathbb{R}$ and $m\in\mathbb{N}$ with $|U|+1+m=d$. For an outcome $\omega=(\omega_S,\omega_T)$, a letter $i<M$ and $y\in\mathbb{R}$ define the local test
--   $$Q(\omega,i,y)=\omega_S\bigl(U,i,\kappa_{b(Ui)}(y)\bigr)\wedge\omega_T\bigl(\lambda,\kappa_{b(\lambda)}(y)\bigr),\qquad \lambda=\rho^{\omega_S}_m(Ui,y).$$
--   Let $\ell=r_W(d-|U|)$, the common window length of the edges $Ui$.
--
--   **Theorem.** There is a finite set $R\subseteq[1,2]$ with $|R|\le 1+M\,\ell\,2^{2\ell+2}$ such that for every $t\in[1,2]$ there is $t'\in R$ with
--
--   $$Q\bigl(\omega,i,\,x+t'\,2^{-(a(Ui)+j)}\bigr)=Q\bigl(\omega,i,\,x+t\,2^{-(a(Ui)+j)}\bigr)$$
--
--   for every outcome $\omega=(\omega_S,\omega_T)$, every $i<M$ and every $j\in\{0,\dots,\ell-1\}$.
--
--   Thus the continuum of scales $t\in[1,2]$ can be replaced, simultaneously for all outcomes of the selector and terminal tables, all nondefault children $i$ of $U$ and all scales $a(Ui)+j$ in their windows, by a deterministic set of at most $1+M\ell\,2^{2\ell+2}$ representatives. No grid-factorization or padding hypotheses remain: both are supplied by the window datum.
--
--   **Formalization Note** The test $Q$ enters as an arbitrary function together with its defining equation `hQ`; the resolutions are `FiniteTableModel.selectorEndpoints W` and `FiniteTableModel.terminalEndpoints W`; the choice map $\chi_{\omega_S}$ is `choose ωS`, linked to `rule` by `hchoose`; and $\ell$ is `W.r (d - U.val.length)`. The depth condition is `hdepth : ∀ i : Fin M, (U.val ++ [i.castSucc]).length + r = d` with our $m$ being `r`; for $M\ge1$ it is the condition $|U|+1+m=d$, and for $M=0$ it is vacuous (there are then no tests to compare).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowLocalFactor.lean#L123-L160

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

theorem OAI.Problem310.WindowLocalFactor.exists_concrete_local_representatives {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀) (U : FiniteTableModel.Node M d) (x : ℝ)
    (choose : FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) →
      List (FiniteTableModel.Child M) → ℝ → FiniteTableModel.Child M)
    (rule : List (FiniteTableModel.Child M) → (Fin M → Bool) → FiniteTableModel.Child M)
    (hchoose : ∀ ωS P y, choose ωS P y = rule P (fun j =>
      FiniteTableModel.selectorValue (FiniteTableModel.selectorEndpoints W) ωS P j y))
    (r : ℕ) (hdepth : ∀ i : Fin M, (U.val ++ [i.castSucc]).length + r = d)
    (Q : (FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) ×
      FiniteTableModel.TerminalTable (FiniteTableModel.terminalEndpoints W)) →
        Fin M → ℝ → Bool)
    (hQ : ∀ ω i y, Q ω i y =
      (ω.1 (FiniteTableModel.selectorAddress (FiniteTableModel.selectorEndpoints W) U i y) &&
        ω.2 (FiniteTableModel.terminalAddress (FiniteTableModel.terminalEndpoints W)
          (FiniteLocalPredicate.localLeaf (choose ω.1) r (U.val ++ [i.castSucc]) (hdepth i) y) y))) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ ω (i : Fin M) (j : Fin (W.r (d - U.val.length))),
          Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) =
            Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) := by sorry
