-- Prove2me | Theorems.Thm_OAI_Problem310_exists_windowData_selector_stability
-- name    : OAI.Problem310.exists_windowData_selector_stability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:24:17.593323+00:00
-- url     : https://prove2.me/theorems/275cd40e-e729-4817-8b85-800ef3bb365a
-- title:
--   A uniform gap makes dyadic selector-table lookups stable off a periodic set of small density
-- statement:
--   Fix natural numbers $M$ and $d$ and a real number $p>0$. Words over the alphabet $\{0,1,\dots,M\}$ are the vertices of the complete $(M+1)$-ary rooted tree: the empty word is the root and $Pc$ is the child $c$ of $P$. The letter $M$ is the *default child* and the letters $0,\dots,M-1$ are the *nondefault children*. A word $P$ of length $|P|<d$ is an *internal node*, and a nonempty word $P$ with $|P|\le d$ is an *edge* (the edge entering the vertex $P$).
--
--   **Window data.** For $q,d,g,r_0\in\mathbb{N}$, a *window datum* $W$ with parameters $(q,d,g,r_0)$ consists of a function $r:\mathbb{N}\to\mathbb{N}$ and three functions $a,b,b^{*}$ from words over $\{0,\dots,q-1\}$ to $\mathbb{N}$ such that, writing $\ell(P)=r(d+1-|P|)$, the following hold for all edges $P,Q$:
--
--   - $\ell(P)\ge 1$ and $\ell(P)\ge r_0$;
--   - $a_P\ge 3$ and $b_P+1=a_P+\ell(P)$, so the *window* of $P$ is the integer interval $[a_P,b_P]$ of length $\ell(P)$;
--   - if $P$ is a proper prefix of $Q$, then $b_P+g<a_Q$;
--   - if $P=Ui$ and $Q=UjV$ for words $U,V$ and letters $i<j$, then $b_P+g<a_Q$;
--   - if $P$ is a prefix of $Q$ (including $P=Q$), then $b_P\le b_Q\le b^{*}_P$;
--   - $b^{*}_P+1\le a_P+2\ell(P)$.
--
--   **Cells and selector tables.** For $\beta\in\mathbb{N}$ and $x\in\mathbb{R}$ let
--   $$\kappa_\beta(x)=\bigl\lfloor 2^{\beta+2}\{x\}\bigr\rfloor\in\{0,1,\dots,2^{\beta+2}-1\},\qquad \{x\}=x-\lfloor x\rfloor,$$
--   the index of the cell of the grid $2^{-(\beta+2)}\mathbb{Z}$, taken modulo $1$, that contains $x$. For a window datum $W$ with parameters $(M+1,d,g,r_0)$, an internal node $P$ and $i\in\{0,\dots,M-1\}$, put $\beta_W(P,i)=b_{Pi}$, the right endpoint of the window of the edge from $P$ to its nondefault child $i$. A *selector table* for $W$ is an arbitrary function $\omega$ assigning a bit $\omega(P,i,k)\in\{0,1\}$ to every internal node $P$, every $i\in\{0,\dots,M-1\}$ and every $k\in\{0,\dots,2^{\beta_W(P,i)+2}-1\}$; its *selector value* at $x\in\mathbb{R}$ is $S_\omega(P,i,x)=\omega\bigl(P,i,\kappa_{\beta_W(P,i)}(x)\bigr)$.
--
--   **Theorem.** There is a natural number $g\ge 2$, depending only on $M$, $d$ and $p$, such that for every $r_0\in\mathbb{N}$ and every window datum $W$ with parameters $(M+1,d,g,r_0)$ there is a set $G\subseteq\mathbb{R}$ with the following properties:
--
--   1. $G$ is a Borel set;
--   2. $G$ is $1$-periodic: $x+1\in G$ if and only if $x\in G$, for every $x\in\mathbb{R}$;
--   3. $\lambda\bigl((\mathbb{R}\setminus G)\cap[0,1]\bigr)\le p$, where $\lambda$ denotes Lebesgue measure;
--   4. for every $x\in G$, every internal node $P$, every $i\in\{0,\dots,M-1\}$, every $n\in\mathbb{N}$ with $\beta_W(P,i)+g<n$, every $t\in[1,2]$ and every selector table $\omega$ for $W$,
--   $$S_\omega\bigl(P,i,\;x+t\,2^{-n}\bigr)=S_\omega(P,i,x).$$
--
--   Because $\omega$ is arbitrary, item 4 says equivalently that $\kappa_{\beta_W(P,i)}(x+t2^{-n})=\kappa_{\beta_W(P,i)}(x)$: every trial point $x+t2^{-n}$ at a scale more than $g$ steps beyond the window endpoint $\beta_W(P,i)$ lies in the same dyadic cell of mesh $2^{-(\beta_W(P,i)+2)}$ (modulo $1$) as $x$.
--
--   In a random tree-routing construction in which the decision at node $P$ about child $i$ is read from the cell of the current point at resolution $\beta_W(P,i)$, this result supplies a large periodic set of stable centers: for $x\in G$ the trial points $x+t2^{-n}$ at all sufficiently fine dyadic scales read exactly the same selector bits as $x$, whatever the tables are. The order of quantifiers is essential: $g$ is fixed before $r_0$ and before the window datum (whose construction may itself depend on $g$), and the exceptional density $p$ does not depend on the window resolutions.
--
--   **Formalization Note** Words are lists over `Fin (M+1)`; the internal nodes form the subtype `Node M d` of lists of length less than $d$, and a nondefault child $i$ of type `Fin M` is the letter `i.castSucc`, the default child being `Fin.last M`. A window datum is the structure `WindowData q d g r₀` with fields `r`, `a`, `b`, `bstar` and the six axioms listed above, which are required only on edges (`ValidWindowEdge`). The cell index $\kappa_\beta$ is `GridSeparation.dyadicKey β`, valued in `Fin (2 ^ (β + 2))`; a selector table is a Boolean function on the addresses $\langle (P,i),k\rangle$ (`SelectorTable`), and `selectorValue` reads it at `selectorAddress` (it is defined on all lists but is only evaluated at internal nodes here). Measurability (`MeasurableSet G`) refers to the Borel $\sigma$-algebra of $\mathbb{R}$, Lebesgue measure is `MeasureTheory.volume`, the measure bound reads `volume (Gᶜ ∩ Icc 0 1) ≤ ENNReal.ofReal p`, and the displacement is written `t * (2⁻¹) ^ n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowDataStability.lean#L12-L43

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridStability
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowPlacement
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowRecursion
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PackedWindowSpan
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorder
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorderRank
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PreorderIndex
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowSpanSum
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreeSpanBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowDataExistence

open OAI OAI.Problem310
open FiniteTableModel

theorem OAI.Problem310.exists_windowData_selector_stability (M d : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ ∀ r₀ : ℕ, ∀ W : WindowData (M + 1) d g r₀,
      ∃ G : Set ℝ, MeasurableSet G ∧
        (∀ x : ℝ, x + 1 ∈ G ↔ x ∈ G) ∧
        MeasureTheory.volume (Gᶜ ∩ Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p ∧
        ∀ x ∈ G, ∀ P : Node M d, ∀ i : Fin M, ∀ n : ℕ,
          W.b (P.val ++ [i.castSucc]) + g < n →
          ∀ t ∈ Set.Icc (1 : ℝ) 2,
          ∀ ω : SelectorTable (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])),
          selectorValue (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])) ω P.val i (x + t * ((2 : ℝ)⁻¹) ^ n) =
          selectorValue (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])) ω P.val i x := by sorry
