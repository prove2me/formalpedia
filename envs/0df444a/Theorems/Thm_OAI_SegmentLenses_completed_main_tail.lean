-- Prove2me | Theorems.Thm_OAI_SegmentLenses_completed_main_tail
-- name    : OAI.SegmentLenses.completed_main_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:21:53.363997+00:00
-- url     : https://prove2.me/theorems/23918ce2-f5ee-49de-b31b-bd8626582cff
-- title:
--   Midpoint-lens tail bound for arbitrary functionals in the full dual
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$, where $a\le b$ reads "$a$ is an ancestor of $b$". Assume that $\le$ is a *tree order* (if $a\le c$ and $b\le c$, then $a\le b$ or $b\le a$), that every interval $[a,b]=\{v\in V: a\le v\le b\}$ is finite, and that every vertex has only finitely many ancestors. Assume also that $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$. For a finitely supported $u:V\to\mathbb{R}$ the *segment norm* is
--   $$
--   \|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\Big(\sum_{S\in\mathcal F}\Big(\sum_{v\in S}u(v)\Big)^2\Big)^{1/2},
--   $$
--   where the supremum runs over all finite families $\mathcal F$ of pairwise disjoint segments. Let $J_V$ be the completion of this normed space and $J_V^{*}$ the space of continuous linear functionals on $J_V$, with the operator norm $\|\cdot\|$. Write $e_v\in J_V$ for the image of the indicator function of $v$, and $e_v^{*}\in J_V^{*}$ for the coordinate functional, i.e. the continuous extension of $u\mapsto u(v)$. For a finite set $H\subseteq V$, the *head* and the *tail* of $x\in J_V^{*}$ are
--   $$
--   P_Hx=\sum_{v\in H}x(e_v)\,e_v^{*},\qquad Q_Hx=x-P_Hx .
--   $$
--   A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$.
--
--   **Theorem.** Let $H$ be a finite ancestral subset of $V$. Let $x,y\in J_V^{*}$ with $P_Hx=x$, and let $R\ge0$ be a real number with $\|x+y\|\le R$ and $\|x-y\|\le R$. Then
--   $$
--   \|Q_Hy\|\le 2\sqrt{R^2-\|x\|^2}.
--   $$
--
--   This is the general midpoint-lens inequality. Only $x$ is required to be a finite combination of coordinate functionals over $H$. No condition is placed on $y$: it may be any continuous functional on $J_V$ and need not lie in the closed span of the coordinate functionals. The conclusion says that the tail of $y$ beyond $H$ is small whenever $x$ is a midpoint of two points of the $R$-ball and $\|x\|$ is close to $R$. Specializing $V$ to the forest of bounded-depth words and to the infinite prefix tree gives the two inequalities of the main midpoint-lens theorem.
--
--   **Formalization Note** The hypothesis $P_Hx=x$ is `head H x = x`, equivalently $x(e_v)=0$ for all $v\notin H$. The square root is `Real.sqrt`, which returns $0$ on negative arguments. This convention plays no role, because $2x=(x+y)+(x-y)$ gives $\|x\|\le R$. The structure on $V$ is given by the instance arguments `DecidableEq V`, `PartialOrder V`, `LocallyFiniteOrder V` (finite intervals), `LocallyFiniteOrderBot V` (finite sets of ancestors), `TreeOrder V`, `SegmentSystem V` and `IntervalSegments V`; decidable equality is a technical assumption. The ancestral condition is `Ancestral (· ≤ ·) H`, and $J_V^{*}$ is `FullDual V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/Completed.lean#L87-L114

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
import Definitions.Def_OAI_Analysis_SegmentLenses_Completed

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

theorem OAI.SegmentLenses.completed_main_tail {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x)
    (R : ℝ) (hR : 0 ≤ R) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) := by sorry
