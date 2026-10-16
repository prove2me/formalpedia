-- Prove2me | Theorems.Thm_OAI_Problem310_Construction_periodic_hitting_of_window_failure
-- name    : OAI.Problem310.Construction.periodic_hitting_of_window_failure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:04:27.839308+00:00
-- url     : https://prove2.me/theorems/ba446498-254a-4f0e-b1f1-6d334d12fd19
-- title:
--   Periodic dyadic hitting set from pointwise failure bounds for the random window-table router
-- statement:
--   This theorem turns a pointwise failure estimate for a random periodic set built from dyadic tables on a tree into a deterministic open periodic set that meets every dilate of the dyadic sequence.
--
--   **Tree and window data.** Fix natural numbers $M,d,g,r_0$. A *word* is a finite sequence over the alphabet $\{0,1,\dots,M\}$; the letter $M$ is the *default child* and $0,\dots,M-1$ are the *nondefault children*. Write $|P|$ for the length of a word $P$ and $Pc$ for $P$ followed by the letter $c$. A *node* is a word of length $<d$, a *leaf* is a word of length exactly $d$, and an *edge* is a nonempty word of length $\le d$. Window data $W$ with parameters $(M+1,d,g,r_0)$ consist of functions $r:\mathbb{N}\to\mathbb{N}$ and $a,b,b^{\ast}$ from words to $\mathbb{N}$ such that, writing $\ell(P)=r(d+1-|P|)$, the following hold for all edges $P,Q$:
--
--   - (W1) $1\le\ell(P)$ and $r_0\le\ell(P)$;
--   - (W2) $a(P)\ge3$ and $b(P)+1=a(P)+\ell(P)$;
--   - (W3) $b(P)+g<a(Q)$ whenever $P$ is a proper prefix of $Q$;
--   - (W4) $b(Pi)+g<a(PjT)$ whenever $i<j$ are letters, $T$ is a word, and $Pi$ and $PjT$ are edges;
--   - (W5) $b(P)\le b(Q)\le b^{\ast}(P)$ whenever $P$ is a prefix of $Q$;
--   - (W6) $b^{\ast}(P)+1\le a(P)+2\ell(P)$.
--
--   Thus the edge $P$ owns the window $a(P),a(P)+1,\dots,b(P)$ of $\ell(P)$ consecutive dyadic exponents.
--
--   **Dyadic keys, tables and the law.** For $\beta\in\mathbb{N}$ and $y\in\mathbb{R}$ put $\kappa_\beta(y)=\lfloor 2^{\beta+2}\{y\}\rfloor\in\{0,1,\dots,2^{\beta+2}-1\}$, where $\{y\}=y-\lfloor y\rfloor$; this is the index of the dyadic cell of length $2^{-\beta-2}$ that contains $y$ modulo $1$. An outcome $\omega=(S,T)$ consists of a *selector table* $S_{P,i}:\{0,\dots,2^{b(Pi)+2}-1\}\to\{0,1\}$ for every node $P$ and every $i\in\{0,\dots,M-1\}$, and a *terminal table* $T_L:\{0,\dots,2^{b(L)+2}-1\}\to\{0,1\}$ for every leaf $L$; different tables are different coordinates even when their cell indices coincide. Let $\Omega_W$ be the finite set of all outcomes. For $0\le p\le1$, $\mathbb{P}_p$ denotes the product probability measure on $\Omega_W$ under which every selector entry is a fair bit, every terminal entry equals $1$ with probability $p$, and all entries are independent.
--
--   **Routing and the routed set.** Given selector tables $S$, a word $P$ and a point $y\in\mathbb{R}$, the selector $i<M$ *fires* at $(P,y)$ if $|P|<d$ and $S_{P,i}(\kappa_{b(Pi)}(y))=1$. The choice $c_S(P,y)$ is the smallest firing $i$, or the default child $M$ if no selector fires. Routing $y$ from a word $Q$ for $m$ steps produces the words $Q_0=Q$ and $Q_{k+1}=Q_k\,c_S(Q_k,y)$ for $k<m$; the *routed leaf* $L_S(y)$ is the word obtained by routing $y$ from the empty word for $d$ steps. The *routed set* of $\omega=(S,T)$ is
--
--   $$B_\omega=\big\{y\in\mathbb{R}:\ T_{L_S(y)}\big(\kappa_{b(L_S(y))}(y)\big)=1\big\},$$
--
--   the set of points whose routed leaf has terminal bit $1$ in the cell of the point.
--
--   **Exceptional centers.** For $B\subseteq\mathbb{R}$, a point $x$ is an *exceptional center* of $B$ if some dilate of the dyadic sequence based at $x$ misses $B$ entirely:
--
--   $$\mathcal{E}(B)=\big\{x\in\mathbb{R}:\ \exists\,t\in[1,2]\ \ \forall n\ge1:\ x+t\,2^{-n}\notin B\big\}.$$
--
--   **Theorem.** Let $W$ be window data with parameters $(M+1,d,g,r_0)$ and let $0<p<1$. Let $\lambda$ be Lebesgue measure and let $G\subseteq\mathbb{R}$ be a Borel set such that $\lambda(G^{c}\cap[0,1])\le p$ and every $x\in G$ satisfies
--
--   $$\mathbb{P}_p\big(\{\omega\in\Omega_W:\ x\in\mathcal{E}(B_\omega)\}\big)\le 2p.$$
--
--   Then there is an open set $H\subseteq\mathbb{R}$ with $x+1\in H\iff x\in H$ for all $x\in\mathbb{R}$ such that
--
--   $$\lambda\big(H\cap[0,1]\big)\le 6p\qquad\text{and}\qquad \forall x\in\mathbb{R}\ \ \forall t\in[1,2]\ \ \exists n\ge1:\ x+t\,2^{-n}\in H.$$
--
--   All regularity and first-moment requirements of the random construction are settled here; what remains as input is geometric: a large set $G$ of good centers and the bound $2p$ on the probability that a good center is exceptional. Periodic hitting sets of this kind, available for every $p\in(0,1)$, are the input from which the dyadic affine avoidance theorem is derived: combining dilated and reflected copies of them and taking the complement in $[0,1]$ yields compact sets of measure close to $1$ that contain no nondegenerate affine copy $\{x+s\,2^{-n}:n\ge1\}$ of the dyadic sequence.
--
--   **Formalization Note** The probability is `ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W)) (TerminalAddress (terminalEndpoints W)) p`, where the selector table of $(P,i)$ has resolution $b(Pi)$ and the terminal table of $L$ has resolution $b(L)$. The random set is `RoutedSetDensity.routedSet` and the exceptional set is `Auxiliary.exceptionalCenters` with index set `Ici 1` and the sequence $n\mapsto2^{-n}$. Lebesgue measure is `volume` with values in $[0,\infty]$, the bounds enter through `ENNReal.ofReal`, and $G$ is assumed `MeasurableSet` for the Borel $\sigma$-algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/Construction.lean#L15-L47

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope

open OAI OAI.Problem310
open Set MeasureTheory FiniteTableModel

theorem OAI.Problem310.Construction.periodic_hitting_of_window_failure
    {M d g r₀ : ℕ} (W : WindowData (M + 1) d g r₀)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hgood : ∀ x ∈ G,
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp.le hp1.le
        {ω | x ∈ Auxiliary.exceptionalCenters
          (RoutedSetDensity.routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
          (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by sorry
