-- Prove2me | Theorems.Thm_OAI_SegmentLenses_SegmentFamily_tail_replacement
-- name    : OAI.SegmentLenses.SegmentFamily.tail_replacement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:15:57.853763+00:00
-- url     : https://prove2.me/theorems/3196fef7-7512-4528-9210-5728610436c0
-- title:
--   Gate expansion of the tail of a replacement representation
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$. The family seminorm of a segment family $\mathcal F$ is $\|u\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}u(S)^2\big)^{1/2}$, and the segment norm is $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\|u\|_{\mathcal F}$, the supremum over all segment families.
--
--   Let $J_V$ be the completion of the finitely supported functions under $\|\cdot\|_{\mathrm{seg}}$. Finitely supported functions are regarded as elements of $J_V$, and $e_v=\delta_v$ are the unit vectors. Let $J_V^{*}$ be the continuous dual of $J_V$ with the operator norm, let $e_v^{*}\in J_V^{*}$ be the coordinate functional extending $u\mapsto u(v)$, and put $\sigma_S=\sum_{v\in S}e_v^{*}$ for finite $S\subseteq V$, so that $\sigma_S(u)=u(S)$. For finite $H\subseteq V$ the head and tail of $x\in J_V^{*}$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^{*}$ and $Q_Hx=x-P_Hx$. A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$. A vertex $g$ is a *gate* of a finite set $H$ if $g\notin H$ and every $v<g$ lies in $H$.
--
--   For finitely supported $p:V\to\mathbb{R}$ and a segment family $\mathcal F$, the replacement representation of $p$ over $\mathcal F$ has coefficients $p(S)$, $S\in\mathcal F$, so its value is $\sum_{S\in\mathcal F}p(S)\,\sigma_S$. The boundary sum $\partial_{\mathcal F}p(g)=\sum_{S\in\mathcal F,\ g\in S}p(S)$ is the total of $p$ over the member containing $g$, or $0$. For a segment family $\mathcal F$, a finite set $H\subseteq V$ and a vertex $g\in V$, the *gate tail* $\tau_{\mathcal F,H}(g)$ is $S\setminus H$ if some member $S\in\mathcal F$ contains $g$ (this member is unique, since the members are pairwise disjoint), and $\emptyset$ otherwise.
--
--   Let $\mathcal F$ be a segment family, let $H,K\subseteq V$ be finite with $H$ ancestral and every member of $\mathcal F$ contained in $K$, and let $p$ be finitely supported with $p(v)=0$ for all $v\notin H$. Then
--   $$
--   Q_H\Big(\sum_{S\in\mathcal F}p(S)\,\sigma_S\Big)=\sum_{g\in K,\ g\ \text{a gate of}\ H}\partial_{\mathcal F}p(g)\;\sigma_{\tau_{\mathcal F,H}(g)} .
--   $$
--
--   The tail of the replacement representation is thereby reorganized gate by gate. A member that carries nonzero mass of $p$ and leaves $H$ crosses out of $H$ through exactly one gate. It contributes its total mass times the segment functional of its part outside $H$. Combined with the cone reconstruction bound, this controls the tail of averaged replacement representations by the averaged absolute boundary sums at the gates.
--
--   **Formalization Note** The left-hand side is `tail H (F.replacement p).value`, and the sum on the right runs over the elements of `K.filter (Gate H)`. The section works with classical decidability (`open scoped Classical`), and the support hypothesis is `p.support ⊆ H`. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/GateRecovery.lean#L222-L249

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

open OAI OAI.SegmentLenses OAI.SegmentLenses.SegmentFamily
open scoped BigOperators
open Finset
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem OAI.SegmentLenses.SegmentFamily.tail_replacement (F : SegmentFamily V) {H K : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (hK : ∀ S ∈ F.sets, S ⊆ K) :
    tail H (F.replacement p).value =
      ∑ g : K.filter (Gate H), F.boundary p g.val • segmentFunctional (F.gateTail H g.val) := by sorry
