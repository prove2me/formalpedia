-- Prove2me | Theorems.Thm_OAI_Problem310_CenterFailureBound_raw_failure_le_of_center_atoms
-- name    : OAI.Problem310.CenterFailureBound.raw_failure_le_of_center_atoms
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:21:51.888508+00:00
-- url     : https://prove2.me/theorems/5e085be2-b061-4a43-983b-5431f33aeb72
-- title:
--   Failure probability at a center is at most $2p$ given atomwise bounds on the center exposure
-- statement:
--   **Setting (finite table model).** Fix $M,d\in\mathbb{N}$. Children are labelled $0,\dots,M$, with $M$ the *default* child; a *node* is a word $P$ over $\{0,\dots,M\}$ of length $|P|<d$, and a *leaf* is a word of length $d$. For a resolution $r\in\mathbb{N}$ and $x\in\mathbb{R}$ let $\kappa_r(x)=\lfloor 2^{r+2}\{x\}\rfloor\in\{0,\dots,2^{r+2}-1\}$ be the dyadic key of $x$, where $\{x\}=x-\lfloor x\rfloor$. Resolutions $b_S(P,i)\in\mathbb{N}$ are given for every node $P$ and selector index $i\in\{0,\dots,M-1\}$, and $b_T(L)\in\mathbb{N}$ for every leaf $L$. A *selector table* $\omega_S$ assigns a bit to each triple $(P,i,k)$ with $k<2^{b_S(P,i)+2}$, and a *terminal table* $\omega_T$ assigns a bit to each pair $(L,k)$ with $k<2^{b_T(L)+2}$. The outcome space $\Omega$ is the finite set of pairs $\omega=(\omega_S,\omega_T)$, and $\mu$ is an arbitrary probability measure on $\Omega$.
--
--   Fix a center $x\in\mathbb{R}$. The selector bit of a node $P$ and index $i$ is $\sigma_{P,i}(\omega)=\omega_S\bigl(P,i,\kappa_{b_S(P,i)}(x)\bigr)$ (and $\mathrm{false}$ for words of length at least $d$). The *center choice* at $P$ is the first-success child: the least $i<M$ with $\sigma_{P,i}(\omega)=\mathrm{true}$, or $M$ if there is none. The *center route* starts at the empty word and appends the center choice $d$ times. Define:
--
--   - the *no-default event* $\mathcal N_x$: the center route never chooses $M$ in its first $d$ steps;
--   - the *center exposure* $\xi_x(\omega)=\bigl(\sigma_{P,i}(\omega)\bigr)_{P,i}$, a bit pattern indexed by pairs (node, selector index), and for each pattern $\xi$ the *center atom* $\mathcal A_x(\xi)=\{\omega:\xi_x(\omega)=\xi\}$;
--   - a pattern $\xi$ is *good* if the first-success route computed from the bits $\xi$ chooses the default child at some depth $k<d$.
--
--   Finally let $B:\Omega\to\mathcal P(\mathbb{R})$ be any random subset of $\mathbb{R}$ and $N\subseteq\mathbb{N}$, and let the *failure event* at $x$ be
--   $$\mathcal F_x=\bigl\{\omega\in\Omega:\ \exists\,t\in[1,2]\ \ \forall n\in N,\ \ x+t\,2^{-n}\notin B(\omega)\bigr\},$$
--   i.e. $x$ is an exceptional center of $B(\omega)$ for the sequence $2^{-n}$.
--
--   **Theorem.** Let $p\ge 0$ be real. If $\mu(\mathcal N_x)\le p$ and $\mu\bigl(\mathcal F_x\cap\mathcal A_x(\xi)\bigr)\le p\,\mu\bigl(\mathcal A_x(\xi)\bigr)$ for every good pattern $\xi$, then
--   $$\mu(\mathcal F_x)\le 2p .$$
--
--   The failure probability at a center thus splits into the probability that the center route never meets the default and a uniform conditional bound on each atom of the center exposure on which it does. This is the finite-exposure union bound, instantiated for the canonical selector and terminal tables, and it reduces the pointwise failure estimate to an estimate conditional on everything the selectors reveal at $x$.
--
--   **Formalization Note** Nodes, leaves and table addresses are the types `Node M d`, `Leaf M d`, `SelectorAddress bS` and `TerminalAddress bT`. A pattern is good (`GoodExposure`) when the route of its canonical completion (all unexposed selector bits set to false) reaches the default, which is the same as for every table in its atom. The event $\mathcal F_x$ is not assumed measurable ($\mu$ of a non-measurable set is its outer measure), and $p$ enters as `ENNReal.ofReal p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/CenterFailureBound.lean#L28-L62

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

open OAI OAI.Problem310 OAI.Problem310.CenterFailureBound
open Set MeasureTheory
open FiniteTableModel CenterRouteExposure

theorem OAI.Problem310.CenterFailureBound.raw_failure_le_of_center_atoms {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (μ : Measure (SelectorTable bS × TerminalTable bT)) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 ≤ p) (B : SelectorTable bS × TerminalTable bT → Set ℝ)
    (N : Set ℕ) (x : ℝ)
    (hbad : μ (noDefaultEvent bS bT x) ≤ ENNReal.ofReal p)
    (hatom : ∀ ξ : Node M d × Fin M → Bool, GoodExposure bS x ξ →
      μ ({ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
          centerAtom bS bT x ξ) ≤
        ENNReal.ofReal p * μ (centerAtom bS bT x ξ)) :
    μ {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ≤
      ENNReal.ofReal (2 * p) := by sorry
