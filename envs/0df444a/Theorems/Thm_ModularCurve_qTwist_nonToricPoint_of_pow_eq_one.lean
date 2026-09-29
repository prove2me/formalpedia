-- Prove2me | Theorems.Thm_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one
-- name    : ModularCurve.qTwist_nonToricPoint_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/bd1570ba-e1a1-56fc-a8cb-ae2761fb9828
-- title:
--   Inertia twist q ↦ ζ q on non-toric Tate points
-- statement:
--   Let $K$ be a commutative ring, let $M$ be a natural number with $M \neq 0$, let $\zeta$ be a unit of $K$ satisfying $\zeta^M = 1$, let $c$ be a unit of $K$, and let $j$ be a natural number with $0 < j$ and $j < M$. For parameters $(K, M, c, j)$ the pair `nonToricPoint K M c j` consists of the two Laurent series over $K$ obtained by viewing as Laurent series the one-variable power series $\mathrm{slotSubst}(K,M,c,j)$ applied to the two universal integral two-variable power series `tateUnivX` and `tateUnivY`, whose coefficient at a bi-exponent $e = (e_0,e_1)$ is $-2\sigma_1(e_1)$, respectively $\sigma_1(e_1)$, when $e_0 = e_1$, and otherwise is $|e_0 - e_1|$, respectively $\binom{e_0-e_1}{2}$ or $-\binom{e_1-e_0+1}{2}$ according to the sign of $e_0-e_1$, whenever $|e_0-e_1|$ divides $e_1$, and $0$ otherwise; here $\mathrm{slotSubst}$ is substitution of the family `slotFamily K M c j` into the two formal variables. Let $\mathrm{qTwist}\,\zeta$ be the ring endomorphism of Laurent series over $K$ that multiplies the coefficient in degree $k \in \mathbb{Z}$ by $\zeta^{k}$. The assertion is that applying $\mathrm{qTwist}\,\zeta$ to each of the two coordinates of `nonToricPoint K M c j` yields exactly `nonToricPoint K M (c * ζ ^ j) j`.
--
--   This records the action of the substitution $q \mapsto \zeta q$ — the inertia generator of $K((q))$ over $K((q^M))$, which fixes the coefficients of the Tate curve $\mathrm{Tate}(q^M)$ — on the non-toric $M$-torsion points, those of parameter $c\,q^j$ with $0 < j < M$: the twist changes the parameter $c$ into $c\zeta^{j}$ and leaves $j$ unchanged. Both coordinates are compared through the explicit coefficient formulas [`ModularCurve.coeff_slotSubst_tateUnivX`](thm.html#ModularCurve.coeff_slotSubst_tateUnivX) and [`ModularCurve.coeff_slotSubst_tateUnivY`](thm.html#ModularCurve.coeff_slotSubst_tateUnivY), and the result feeds into [`ModularCurve.exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot`](thm.html#ModularCurve.exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot), where the inertia action on $\mathrm{Tate}(q^M)[M]$ is identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

universe u in

theorem ModularCurve.qTwist_nonToricPoint_of_pow_eq_one
    (K : Type u) [CommRing K] (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ)
    (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    (qTwist ζ (nonToricPoint K M c j).1, qTwist ζ (nonToricPoint K M c j).2) =
      nonToricPoint K M (c * ζ ^ j) j := by sorry
