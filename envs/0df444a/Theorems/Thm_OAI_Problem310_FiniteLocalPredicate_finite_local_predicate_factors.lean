-- Prove2me | Theorems.Thm_OAI_Problem310_FiniteLocalPredicate_finite_local_predicate_factors
-- name    : OAI.Problem310.FiniteLocalPredicate.finite_local_predicate_factors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:33:24.44876+00:00
-- url     : https://prove2.me/theorems/3ba460b4-89d4-4a37-8673-98189cb05ffc
-- title:
--   A local selector-and-terminal test is constant on the cells of a common fine dyadic grid
-- statement:
--   Fix $M,d\in\mathbb{N}$. Finite words over $\{0,1,\dots,M\}$ are the vertices of the complete $(M+1)$-ary tree (the letter $M$ is the default child); a *node* is a word of length $<d$, a *leaf* is a word of length exactly $d$, and $P\sqsubseteq Q$ means that $P$ is a prefix of $Q$. For $\beta\in\mathbb{N}$ and $y\in\mathbb{R}$ let $\kappa_\beta(y)=\lfloor 2^{\beta+2}\{y\}\rfloor$, where $\{y\}=y-\lfloor y\rfloor$.
--
--   Let $b_S(Q,j)\in\mathbb{N}$ (for nodes $Q$ and $j<M$) and $b_T(L)\in\mathbb{N}$ (for leaves $L$) be resolutions, let $\omega_S$ be a selector table (a bit $\omega_S(Q,j,c)$ for each $c<2^{b_S(Q,j)+2}$) and $\omega_T$ a terminal table (a bit $\omega_T(L,c)$ for each $c<2^{b_T(L)+2}$). The selector bit of $(Q,j)$ at $y$ is $\sigma_{Q,j}(y)=\omega_S(Q,j,\kappa_{b_S(Q,j)}(y))$ if $|Q|<d$, and $\mathrm{false}$ otherwise.
--
--   Let $\chi(Q,y)\in\{0,\dots,M\}$ be a child-choice map computed from the selector bits at $Q$ by an arbitrary deterministic rule: there are functions $R_Q:\{\mathrm{true},\mathrm{false}\}^M\to\{0,\dots,M\}$ with $\chi(Q,y)=R_Q\bigl(\sigma_{Q,0}(y),\dots,\sigma_{Q,M-1}(y)\bigr)$ for all words $Q$ and all $y\in\mathbb{R}$. Starting from a word $P$, let $\rho_0(P,y)=P$ and $\rho_{n+1}(P,y)=\rho_n(P,y)\,\chi(\rho_n(P,y),y)$. Fix $m\in\mathbb{N}$ and a word $P$ with $|P|+m=d$, so that $\lambda(y)=\rho_m(P,y)$ is a leaf. Fix also a node $U$, a letter $i<M$ and $B\in\mathbb{N}$ such that
--
--   - $b_S(Q,j)\le B$ for every node $Q$ with $P\sqsubseteq Q$ and every $j<M$,
--   - $b_T(L)\le B$ for every leaf $L$ with $P\sqsubseteq L$,
--   - $b_S(U,i)\le B$.
--
--   **Theorem.** If $x,y\in\mathbb{R}$ satisfy $\lfloor 2^{B+2}\{x\}\rfloor=\lfloor 2^{B+2}\{y\}\rfloor$, then
--
--   $$\omega_S\bigl(U,i,\kappa_{b_S(U,i)}(x)\bigr)\wedge\omega_T\bigl(\lambda(x),\kappa_{b_T(\lambda(x))}(x)\bigr)=\omega_S\bigl(U,i,\kappa_{b_S(U,i)}(y)\bigr)\wedge\omega_T\bigl(\lambda(y),\kappa_{b_T(\lambda(y))}(y)\bigr).$$
--
--   Each side is a *local test*: the selector of the edge $(U,i)$ succeeds and the terminal bit read at the leaf reached by routing through the subtree below $P$ is $\mathrm{true}$. The theorem says that, for any fixed tables, this test is constant on each cell of the periodic dyadic grid of mesh $2^{-(B+2)}$ as soon as $B$ dominates every resolution involved. No property of the rules $R_Q$ is needed; in applications they form the first-success rule with default, and $P$ is the word $U$ followed by $i$. This factorization is what later allows the continuous scale parameter of an affine copy of the dyadic sequence to be replaced by finitely many representatives.
--
--   **Formalization Note** The choice map and the rules are `choose` and `rule`, linked by the hypothesis `hchoose`; the leaf $\lambda(y)$ is `localLeaf choose r P hdepth y`, where `r` is our $m$. The node $U$ is not required to be related to $P$ in the statement. The conjunction is Boolean `&&`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FiniteLocalPredicate.lean#L35-L73

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

open OAI OAI.Problem310 OAI.Problem310.FiniteLocalPredicate
open RoutingPath GridSeparation FiniteTableModel
variable {M d : ℕ}

theorem OAI.Problem310.FiniteLocalPredicate.finite_local_predicate_factors
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (choose : List (Child M) → ℝ → Child M)
    (rule : List (Child M) → (Fin M → Bool) → Child M)
    (hchoose : ∀ Q x, choose Q x = rule Q (fun i => selectorValue bS ωS Q i x))
    (r : ℕ) (P : List (Child M)) (hdepth : P.length + r = d)
    (U : Node M d) (i : Fin M) (B : ℕ)
    (hbS : ∀ Q : Node M d, P.IsPrefix Q.val → ∀ j, bS Q j ≤ B)
    (hbT : ∀ L : Leaf M d, P.IsPrefix L.val → bT L ≤ B)
    (hIn : bS U i ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    (ωS (selectorAddress bS U i x) &&
      ωT (terminalAddress bT (localLeaf choose r P hdepth x) x)) =
    (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT (localLeaf choose r P hdepth y) y)) := by sorry
