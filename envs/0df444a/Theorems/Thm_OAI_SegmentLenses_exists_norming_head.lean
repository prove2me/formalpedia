-- Prove2me | Theorems.Thm_OAI_SegmentLenses_exists_norming_head
-- name    : OAI.SegmentLenses.exists_norming_head
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:10:20.424439+00:00
-- url     : https://prove2.me/theorems/a310b449-98a0-4df4-8b19-e9b669b0fddc
-- title:
--   A dual functional supported on a finite ancestral set is normed by a unit test supported there
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$. The family seminorm of a segment family $\mathcal F$ is $\|u\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}u(S)^2\big)^{1/2}$, and the segment norm is $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\|u\|_{\mathcal F}$, the supremum over all segment families.
--
--   Let $J_V$ be the completion of the finitely supported functions under $\|\cdot\|_{\mathrm{seg}}$. Finitely supported functions are regarded as elements of $J_V$, and $e_v=\delta_v$ are the unit vectors. Let $J_V^{*}$ be the continuous dual of $J_V$ with the operator norm, let $e_v^{*}\in J_V^{*}$ be the coordinate functional extending $u\mapsto u(v)$, and put $\sigma_S=\sum_{v\in S}e_v^{*}$ for finite $S\subseteq V$, so that $\sigma_S(u)=u(S)$. For finite $H\subseteq V$ the head and tail of $x\in J_V^{*}$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^{*}$ and $Q_Hx=x-P_Hx$. A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$.
--
--   Let $H\subseteq V$ be finite and ancestral, and let $x\in J_V^{*}$ satisfy $P_Hx=x$ and $x\ne0$. Then there is a finitely supported $q:V\to\mathbb{R}$ with
--   $$
--   q(v)=0\ \text{ for all } v\notin H,\qquad\|q\|_{\mathrm{seg}}=1,\qquad x(q)=\|x\|_{J_V^{*}} .
--   $$
--
--   So the dual norm of a functional supported on a finite ancestral set is attained, at a unit test vector supported on the same set. In the midpoint-lens argument, the multiple $\|x\|\,q$ is the test vector used in the finite tail bound: it has segment norm $\|x\|$ and pairs with $x$ to give $\|x\|^2$.
--
--   **Formalization Note** The test is an element of `Test V`, which is `V →₀ ℝ` with the segment norm; the support condition is `p.coeff.support ⊆ H`. The pairing $x(q)$ is evaluation at the image `(p : Primal V)` of the test in the completion. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/HeadTests.lean#L107-L125

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem OAI.SegmentLenses.exists_norming_head {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x : FullDual V) (hx : head H x = x) (hne : x ≠ 0) :
    ∃ p : Test V, p.coeff.support ⊆ H ∧ ‖p‖ = 1 ∧ x (p : Primal V) = ‖x‖ := by sorry
