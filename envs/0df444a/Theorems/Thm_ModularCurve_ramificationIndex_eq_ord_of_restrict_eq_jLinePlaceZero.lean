-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndex_eq_ord_of_restrict_eq_jLinePlaceZero
-- name    : ModularCurve.ramificationIndex_eq_ord_of_restrict_eq_jLinePlaceZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/5c7d51f8-f581-57c8-b93d-0960523f2ff4
-- title:
--   Ramification index over j=0 equals ord_w(j)
-- statement:
--   Fix $N \ge 1$ and let $F_N = \mathbb{Q}(j_q, j_q|_{q \mapsto q^N})$ be the intermediate field [`ModularCurve.modularFunctionField N`](def/ModularCurve_X0.html#L250) of the Laurent series field $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansion $j_q$ of the modular invariant and by its image under the $N$-fold substitution `qExpand ℚ N`; it is regarded as an algebra over the subfield $\mathbb{Q}\langle j_q\rangle$ via the inclusion [`ModularCurve.jAdjoinRingHom`](def/ModularCurve_RouteBCoordRing.html#L14), and it is assumed integral over $\mathbb{Q}\langle j_q\rangle$. Let $w$ be a place of $F_N$ over $\mathbb{Q}$, that is, a valuation subring of $F_N$ which contains the image of $\mathbb{Q}$, is not all of $F_N$ and is a principal ideal ring. Assume that the restriction of $w$ to $\mathbb{Q}\langle j_q\rangle$ — the preimage of its valuation subring under the inclusion — is the place [`ModularCurve.jLinePlaceZero`](def/ModularCurve_JLinePlaces.html#L54), the place of $\mathbb{Q}\langle j_q\rangle$ obtained by transporting, along the isomorphism $\operatorname{RatFunc} \mathbb{Q} \cong \mathbb{Q}\langle j_q\rangle$ coming from the transcendence of $j_q$, the finite place of $\operatorname{RatFunc} \mathbb{Q}$ attached to $X - 0$. Then the ramification index of $w$ over $\mathbb{Q}\langle j_q\rangle$, namely the least $n > 0$ such that $\operatorname{ord}_w(f) = n$ for some nonzero $f$ in $\mathbb{Q}\langle j_q\rangle$, equals, as an integer, $\operatorname{ord}_w$ of the element $j_q$ of $F_N$, where $\operatorname{ord}_w$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation.
--
--   This is the standard identification, for a place of the function field of $X_0(N)$ lying above the place $j = 0$ of the $j$-line, of the ramification index with the order of vanishing of $j$ at that place. It is used in the counts of fibres of the covering $X_0(N) \to X(1)$ over the elliptic points, in [`ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree`](thm.html#ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree) and [`ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo`](thm.html#ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndex_eq_ord_of_restrict_eq_jLinePlaceZero.lean

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve

theorem ModularCurve.ramificationIndex_eq_ord_of_restrict_eq_jLinePlaceZero (N : ℕ) [NeZero N] :
    letI := ModularCurve.jAdjoinAlgebra N
    ∀ [Algebra.IsIntegral ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N)]
      (w : AlgebraicCurve.Place ℚ ↥(ModularCurve.modularFunctionField N)),
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ = ModularCurve.jLinePlaceZero →
      (w.ramificationIndex ↥ℚ⟮ModularCurve.jq⟯ : ℤ) = w.ord (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) := by sorry
