-- Prove2me | Theorems.Thm_OAI_SegmentLenses_Representation_norm_le
-- name    : OAI.SegmentLenses.Representation.norm_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:05:59.362962+00:00
-- url     : https://prove2.me/theorems/d5393873-7106-4f09-b676-0b92b3f4699f
-- title:
--   The dual norm of a segment representation is at most the square root of its energy
-- statement:
--   Let $V$ be a set with a segment system, i.e. a distinguished class of finite subsets of $V$, called segments, that contains every singleton. A *segment family* $\mathcal F$ is a finite set of pairwise disjoint segments. For a finitely supported $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$. The family seminorm of a segment family $\mathcal F$ is $\|u\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}u(S)^2\big)^{1/2}$, and the segment norm is $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\|u\|_{\mathcal F}$, the supremum over all segment families.
--
--   Let $J_V$ be the completion of the finitely supported functions under $\|\cdot\|_{\mathrm{seg}}$. Finitely supported functions are regarded as elements of $J_V$, and $e_v=\delta_v$ are the unit vectors. Let $J_V^{*}$ be the continuous dual of $J_V$ with the operator norm, let $e_v^{*}\in J_V^{*}$ be the coordinate functional extending $u\mapsto u(v)$, and put $\sigma_S=\sum_{v\in S}e_v^{*}$ for finite $S\subseteq V$, so that $\sigma_S(u)=u(S)$.
--
--   A *representation* $A=(\mathcal F,c)$ is a segment family $\mathcal F$ together with real coefficients $(c_S)_{S\in\mathcal F}$. Its value is $\Lambda A=\sum_{S\in\mathcal F}c_S\,\sigma_S\in J_V^{*}$ and its energy is $\mathcal E(A)=\sum_{S\in\mathcal F}c_S^2$. For every representation $A=(\mathcal F,c)$,
--   $$
--   \Big\|\sum_{S\in\mathcal F}c_S\,\sigma_S\Big\|_{J_V^{*}}\le\sqrt{\mathcal E(A)}=\Big(\sum_{S\in\mathcal F}c_S^2\Big)^{1/2}.
--   $$
--
--   So the energy, an $\ell_2$ quantity on the coefficients, controls the dual norm of the value. No order structure on $V$ is needed. In the midpoint tail bound it is applied to the error between a representation and the replacement representation of a norming test, which turns an averaged energy bound into a norm bound.
--
--   **Formalization Note** `A.value` is `∑ S, A.coeff S • segmentFunctional S` in `FullDual V`, the `StrongDual` of the completion `Primal V` of `Test V`. `A.energy` is `∑ S, A.coeff S ^ 2`, and the square root is `Real.sqrt` of this nonnegative number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/Pairing.lean#L159-L174

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [SegmentSystem V]

theorem OAI.SegmentLenses.Representation.norm_le (A : Representation V) :
    ‖A.value‖ ≤ Real.sqrt A.energy := by sorry
