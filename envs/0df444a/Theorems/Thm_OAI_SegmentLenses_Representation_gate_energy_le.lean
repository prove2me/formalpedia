-- Prove2me | Theorems.Thm_OAI_SegmentLenses_Representation_gate_energy_le
-- name    : OAI.SegmentLenses.Representation.gate_energy_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:08:36.932702+00:00
-- url     : https://prove2.me/theorems/105436d3-abe1-4b7f-9bdf-1965f9c62908
-- title:
--   Squared values of a segment representation at the gates of a set are bounded by its energy
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$. The family seminorm of a segment family $\mathcal F$ is $\|u\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}u(S)^2\big)^{1/2}$, and the segment norm is $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\|u\|_{\mathcal F}$, the supremum over all segment families.
--
--   Let $J_V$ be the completion of the finitely supported functions under $\|\cdot\|_{\mathrm{seg}}$. Finitely supported functions are regarded as elements of $J_V$, and $e_v=\delta_v$ are the unit vectors. Let $J_V^{*}$ be the continuous dual of $J_V$ with the operator norm, let $e_v^{*}\in J_V^{*}$ be the coordinate functional extending $u\mapsto u(v)$, and put $\sigma_S=\sum_{v\in S}e_v^{*}$ for finite $S\subseteq V$, so that $\sigma_S(u)=u(S)$.
--
--   A *representation* $A=(\mathcal F,c)$ is a segment family $\mathcal F$ together with real coefficients $(c_S)_{S\in\mathcal F}$. Its value is $\Lambda A=\sum_{S\in\mathcal F}c_S\,\sigma_S\in J_V^{*}$ and its energy is $\mathcal E(A)=\sum_{S\in\mathcal F}c_S^2$. A vertex $g$ is a *gate* of a finite set $H$ if $g\notin H$ and every $v<g$ lies in $H$.
--
--   Let $H\subseteq V$ be finite (not necessarily ancestral), let $G\subseteq V$ be a finite set all of whose elements are gates of $H$, and let $A=(\mathcal F,c)$ be a representation. Then
--   $$
--   \sum_{g\in G}(\Lambda A)(e_g)^2\le\mathcal E(A)=\sum_{S\in\mathcal F}c_S^2 .
--   $$
--
--   Here $(\Lambda A)(e_g)=\sum_{S\in\mathcal F,\ g\in S}c_S$ is the coefficient of the member of $\mathcal F$ containing $g$, or $0$ if there is none. Thus the squared coefficients read off at the gates of any finite set never exceed the total energy of the representation. In the finite midpoint tail bound it is applied to error representations, and bounds their squared values at the gates by their energy.
--
--   **Formalization Note** The sum runs over the elements of the finset `G`, and `unitVector g` is the image of $\delta_g$ in the completion. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/LawRecovery.lean#L263-L302

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem OAI.SegmentLenses.Representation.gate_energy_le (A : Representation V) {H : Finset V}
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g) :
    (∑ g : G, A.value (unitVector g.val) ^ 2) ≤ A.energy := by sorry
