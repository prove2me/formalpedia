-- Prove2me | Theorems.Thm_OAI_Problem310_ConcreteWindowAtom_raw_failure_on_good_atom
-- name    : OAI.Problem310.ConcreteWindowAtom.raw_failure_on_good_atom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:53:23.354699+00:00
-- url     : https://prove2.me/theorems/b54d7abf-4695-40f7-bafe-7c5d13f351d7
-- title:
--   Exceptional-center probability at most $p$ on good center atoms of stable points
-- statement:
--   This theorem bounds, on every good center atom of a stable point $x$, the conditional probability that $x$ is an exceptional center of a random periodic set built from dyadic tables on a tree.
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
--   **Center atoms, good exposures, stability.** Fix $x\in\mathbb{R}$. An *exposure* is a function $\xi$ assigning a bit $\xi(P,i)\in\{0,1\}$ to every node $P$ and every $i<M$; its *center atom* is the event
--
--   $$A_{x,\xi}=\big\{\omega=(S,T)\in\Omega_W:\ S_{P,i}(\kappa_{b(Pi)}(x))=\xi(P,i)\ \text{ for every node } P \text{ and every } i<M\big\}$$
--
--   that the selector entries read at $x$ equal $\xi$. The exposure $\xi$ is *good* if the route of $x$ takes the default child within depth $d$ when the selector tables are $S^{\xi}$, the tables that agree with $\xi$ at the entries read at $x$ and vanish elsewhere: $c_{S^\xi}(Q_k,x)=M$ for some $k<d$, where $Q_0,Q_1,\dots$ is the route of $x$ from the empty word. The point $x$ is *stable* for $W$ if for every node $P$, every $i<M$, every integer $n>b(Pi)+g$ and every $t\in[1,2]$,
--
--   $$\kappa_{b(Pi)}\big(x+t\,2^{-n}\big)=\kappa_{b(Pi)}(x),$$
--
--   so that dyadic perturbations at exponents beyond $b(Pi)+g$ do not change the selector cells read at $x$.
--
--   **Theorem.** Let $W$ be window data with parameters $(M+1,d,g,r_0)$, where $M\ge1$, and let $0\le p\le1$. Assume the budget condition
--
--   $$N\Big(1-\frac p2\Big)^{Mr}\le p\qquad\text{for all integers } r\ge r_0 \text{ and all integers } 0\le N\le 1+M\,r\,2^{2r+2}.$$
--
--   If $x\in\mathbb{R}$ is stable for $W$ and $\xi$ is a good exposure, then
--
--   $$\mathbb{P}_p\Big(\big\{\omega:\ x\in\mathcal{E}(B_\omega)\big\}\cap A_{x,\xi}\Big)\le p\;\mathbb{P}_p\big(A_{x,\xi}\big).$$
--
--   When $\mathbb{P}_p(A_{x,\xi})>0$, this says that, conditionally on the selector bits read at $x$, the probability that some dilate $\{x+t\,2^{-n}:n\ge1\}$ with $t\in[1,2]$ misses the random set $B_\omega$ is at most $p$. Combined with a bound on the probability of the remaining atoms, on which the route of $x$ never takes the default child, it yields the pointwise failure bound $2p$ that feeds the construction of an open periodic set meeting every such dilate.
--
--   **Formalization Note** Stability is `StableAt W x`, which asks that `selectorValue` at $x$ and at $x+t\,2^{-n}$ agree for every selector table; this is equivalent to the equality of dyadic keys displayed above. Goodness is `GoodExposure`, evaluated on `centerCompletion`, the selector table that extends $\xi$ by false off the exposed entries. The probability is `ConcreteLabels.outcomeLaw`, and the exceptional set is `Auxiliary.exceptionalCenters` with index set `Ici 1` and the sequence $n\mapsto2^{-n}$. The budget hypothesis is stated in `ENNReal` with `ENNReal.ofReal (1 - p / 2)`; since $1-p/2\ge1/2>0$ it is equivalent to the real inequality above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ConcreteWindowAtom.lean#L80-L134

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

open OAI OAI.Problem310 OAI.Problem310.ConcreteWindowAtom
open Set MeasureTheory
open scoped ENNReal BigOperators
open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate
open CenterRouteExposure CenterFailureBound WindowExceptionalTransfer WindowTrialAddresses
variable {M d g r₀ : ℕ}

theorem OAI.Problem310.ConcreteWindowAtom.raw_failure_on_good_atom
    (W : WindowData (M + 1) d g r₀) (hM : 1 ≤ M)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbudget : ∀ r : ℕ, r₀ ≤ r → ∀ N : ℕ,
      N ≤ 1 + M * r * 2 ^ (2 * r + 2) →
      (N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) ≤ ENNReal.ofReal p)
    (x : ℝ) (hstable : StableAt W x)
    (ξ : Node M d × Fin M → Bool) (hgood : GoodExposure (selectorEndpoints W) x ξ) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1
      ({ω | x ∈ Auxiliary.exceptionalCenters
        (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
        (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
        centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) ≤
    ENNReal.ofReal p *
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp0 hp1
        (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) := by sorry
