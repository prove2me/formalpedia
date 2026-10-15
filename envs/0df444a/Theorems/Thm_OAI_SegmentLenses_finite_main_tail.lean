-- Prove2me | Theorems.Thm_OAI_SegmentLenses_finite_main_tail
-- name    : OAI.SegmentLenses.finite_main_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:20:58.251438+00:00
-- url     : https://prove2.me/theorems/0aef7465-7740-4df8-bd0b-4d718e60f3f5
-- title:
--   Midpoint-lens tail bound for functionals supported on a finite ancestral set
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$, where $a\le b$ reads "$a$ is an ancestor of $b$". Assume that $\le$ is a *tree order* (if $a\le c$ and $b\le c$, then $a\le b$ or $b\le a$) and that it is locally finite (every interval $[a,b]=\{v\in V: a\le v\le b\}$ is finite). Assume also that $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$. For a finitely supported $u:V\to\mathbb{R}$ the *segment norm* is
--   $$
--   \|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\Big(\sum_{S\in\mathcal F}\Big(\sum_{v\in S}u(v)\Big)^2\Big)^{1/2},
--   $$
--   where the supremum runs over all finite families $\mathcal F$ of pairwise disjoint segments. Let $J_V$ be the completion of this normed space and $J_V^{*}$ the space of continuous linear functionals on $J_V$, with the operator norm $\|\cdot\|$. Write $e_v\in J_V$ for the image of the indicator function of $v$, and $e_v^{*}\in J_V^{*}$ for the coordinate functional, i.e. the continuous extension of $u\mapsto u(v)$. For a finite set $H\subseteq V$, the *head* and the *tail* of $x\in J_V^{*}$ are
--   $$
--   P_Hx=\sum_{v\in H}x(e_v)\,e_v^{*},\qquad Q_Hx=x-P_Hx .
--   $$
--   A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$.
--
--   **Theorem.** Let $H\subseteq K$ be finite ancestral subsets of $V$. Let $x,y\in J_V^{*}$ satisfy $P_Hx=x$ and $P_Ky=y$, and let $R\ge0$ be a real number with $\|x+y\|\le R$ and $\|x-y\|\le R$. Then
--   $$
--   \|Q_Hy\|\le 2\sqrt{R^2-\|x\|^2}.
--   $$
--
--   Here $x$ is the midpoint of $x+y$ and $x-y$, and both of these lie in the closed ball of radius $R$ about the origin. The theorem says that the part of $y$ outside $H$ must be small when $\|x\|$ is close to $R$. For comparison, in a Hilbert space the parallelogram law gives $\|y\|^2\le R^2-\|x\|^2$ for the whole of $y$. Here only the tail of $y$ beyond the ancestral set carrying $x$ is controlled, with the constant $2$. This is the finitely supported case, in which $y$ is a finite combination of coordinate functionals over $K$. The version for arbitrary $y\in J_V^{*}$ is derived from it by localizing to finite ancestral sets.
--
--   **Formalization Note** The hypotheses $P_Hx=x$ and $P_Ky=y$ are `head H x = x` and `head K y = y`. Equivalently, $x(e_v)=0$ for $v\notin H$ and $y(e_v)=0$ for $v\notin K$. The square root is `Real.sqrt`, which returns $0$ on negative arguments. This convention plays no role, because $2x=(x+y)+(x-y)$ gives $\|x\|\le R$, so the radicand is nonnegative. The structure on $V$ is given by the instance arguments `DecidableEq V`, `PartialOrder V`, `LocallyFiniteOrder V`, `TreeOrder V`, `SegmentSystem V` and `IntervalSegments V`; decidable equality is a technical assumption. The ancestral condition is `Ancestral (· ≤ ·) H`, and $J_V^{*}$ is `FullDual V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/TailBudget.lean#L221-L283

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
import Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem OAI.SegmentLenses.finite_main_tail {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) (hy : head K y = y)
    (R : ℝ) (hR : 0 ≤ R) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) := by sorry
