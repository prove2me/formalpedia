-- Prove2me | Theorems.Thm_OAI_Problem310_ConcreteWindowAtom_localMiss_mass
-- name    : OAI.Problem310.ConcreteWindowAtom.localMiss_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:52:45.119714+00:00
-- url     : https://prove2.me/theorems/dc8c7dcb-594a-447e-b239-8555424ca7b6
-- title:
--   Exact miss probability $(1-p/2)^{Mr}$ of the local window trials on a center atom
-- statement:
--   This theorem computes, in a finite random model of dyadic tables attached to a tree, the exact probability that the selector bits read at a point $x$ take prescribed values while every local trial below a fixed node fails at one fixed scale $t$.
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
--   **Routing.** Given selector tables $S$, a word $P$ and a point $y\in\mathbb{R}$, the selector $i<M$ *fires* at $(P,y)$ if $|P|<d$ and $S_{P,i}(\kappa_{b(Pi)}(y))=1$. The choice $c_S(P,y)$ is the smallest firing $i$, or the default child $M$ if no selector fires. Routing $y$ from a word $Q$ for $m$ steps produces the words $Q_0=Q$ and $Q_{k+1}=Q_k\,c_S(Q_k,y)$ for $k<m$.
--
--   **Center atoms and local trials.** Fix $x\in\mathbb{R}$. An *exposure* is a function $\xi$ assigning a bit $\xi(P,i)\in\{0,1\}$ to every node $P$ and every $i<M$. Its *center atom* is the event
--
--   $$A_{x,\xi}=\big\{\omega=(S,T)\in\Omega_W:\ S_{P,i}(\kappa_{b(Pi)}(x))=\xi(P,i)\ \text{ for every node } P \text{ and every } i<M\big\}$$
--
--   that the selector entries read at $x$ equal $\xi$ (the terminal tables are unrestricted). Fix a node $U$ and put $r_U=r(d-|U|)$, the common window length $\ell(Ui)$ of the child edges $Ui$. For $\omega=(S,T)$, $i<M$ and $y\in\mathbb{R}$, the *local test* $Q_\omega(U,i,y)$ equals $1$ exactly when $S_{U,i}(\kappa_{b(Ui)}(y))=1$ and $T_\Lambda(\kappa_{b(\Lambda)}(y))=1$, where $\Lambda$ is the leaf obtained by routing $y$ from the word $Ui$ for $d-|U|-1$ steps. For a scale $t$ the *trial points* are $y_{i,j}(t)=x+t\,2^{-(a(Ui)+j)}$ for $0\le i<M$ and $0\le j<r_U$, and the *local miss event* is
--
--   $$\mathrm{Miss}_U(x,t,\xi)=A_{x,\xi}\cap\big\{\omega:\ Q_\omega(U,i,y_{i,j}(t))=0\ \text{ for all } i<M \text{ and } j<r_U\big\}.$$
--
--   **Theorem.** Let $W$ be window data with parameters $(M+1,d,g,r_0)$, let $U$ be a node, $x\in\mathbb{R}$, $t\in[1,2]$, $0\le p\le1$, and let $\xi$ be an exposure. Then
--
--   $$\mathbb{P}_p\big(\mathrm{Miss}_U(x,t,\xi)\big)=\Big(1-\frac{p}{2}\Big)^{M\,r_U}\,\mathbb{P}_p\big(A_{x,\xi}\big).$$
--
--   Relative to the center atom, the $M r_U$ local trials at a single scale therefore fail together exactly as if they were independent events of probability $p/2$ each (a fair selector fires and an independent terminal bit equals $1$). This exact per-scale formula is the term of a union bound over finitely many representative scales $t$, which shows that on a good center atom the point $x$ is an exceptional center of the random routed set with conditional probability at most $p$.
--
--   **Formalization Note** $\mathbb{P}_p$ is `ConcreteLabels.outcomeLaw`, the product of a uniform law on selector tables and an independent Bernoulli($p$) law on terminal tables; table coordinates are dependent pairs (table name, cell index). The local miss event is `localMiss W U x t ξ`, the center atom is `centerAtom`, the local test is `localQ`, and the trials range over `Fin M × Fin (W.r (d - U.val.length))`. The factor $1-p/2$ enters as `ENNReal.ofReal (1 - p / 2)`, which loses nothing because $1-p/2\ge1/2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ConcreteWindowAtom.lean#L47-L78

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

theorem OAI.Problem310.ConcreteWindowAtom.localMiss_mass (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ξ : Node M d × Fin M → Bool) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1 (localMiss W U x t ξ) =
    (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - U.val.length)) *
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp0 hp1
        (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) := by sorry
