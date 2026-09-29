-- Prove2me | Theorems.Thm_ModularCurve_evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd
-- name    : ModularCurve.evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/a660dbd9-91bd-5d5c-a89d-d95c1fe38044
-- title:
--   Vanishing of (πᵃG)(x) iff stack order at least one
-- statement:
--   Let $K$ be a field with decidable equality and $N$ a nonzero natural number, and let $F_N = K(j(q), j(q^N)) \subseteq K((q))$ denote the intermediate field `modularFunctionFieldC K N` of the Laurent series field generated over $K$ by the $q$-expansion `jqModC K` and its $N$-fold expansion `jqNModC K N`. Let $x$ be a place of $F_N$ over $K$, that is, a proper valuation subring of $F_N$ containing $K$ which is a principal ideal ring, with associated order function $\operatorname{ord}_x$ and evaluation map $\operatorname{evalAt}_x$ (the residue of an element of the valuation subring, pulled back to $K$), and assume $x$ is rational, i.e. $K$ surjects onto its residue field. Write $u =$ `placeWidth N x`, the quotient of `jWidth` $(\operatorname{evalAt}_x j)$, which is $3$, $2$ or $1$ according as $\operatorname{evalAt}_x j$ is $0$, $1728$ or neither, by $\operatorname{ord}_x(j - \operatorname{evalAt}_x j)$ truncated to $\mathbb{N}$. Let $m, a \in \mathbb{Z}$ with $u \ge 1$ and $u\,a = m\,(\mathrm{jWidth}(\operatorname{evalAt}_x j) - 1)$, let $\pi \in F_N$ satisfy $\operatorname{ord}_x \pi = 1$, and let $G \in F_N$ be nonzero with $\operatorname{ord}_x G \ge -a$. Then $\operatorname{evalAt}_x(\pi^a G) = 0$ if and only if $1 \le u\,\operatorname{ord}_x G + m\,(\mathrm{jWidth}(\operatorname{evalAt}_x j) - 1)$, the quantity `stackOrd N m G x`.
--
--   This is the place-by-place criterion identifying the vanishing of the leading term $(\pi^aG)(x)$ of a weight-$2m$ expression with coefficient $G$ against $(dj)^m$ with positivity of its order on the stack at $x$, the allowed pole order being fixed by the exactness condition $u\,a = m(\mathrm{jWidth}-1)$. It is used in [`ModularCurve.SSCarrier.lead_qP_mul_thetaL_zpow_ne_zero`](thm.html#ModularCurve.SSCarrier.lead_qP_mul_thetaL_zpow_ne_zero) and in [`ModularCurve.resFnFun_eq_zero_iff_forall_one_le_stackOrd`](thm.html#ModularCurve.resFnFun_eq_zero_iff_forall_one_le_stackOrd), where the vanishing of a residue-type map is expressed through stack orders at all places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd
    {K : Type*} [Field K] [DecidableEq K] (N : ℕ) [NeZero N]
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x.IsRational) (m a : ℤ)
    (hu : 1 ≤ placeWidth N x)
    (ha : (placeWidth N x : ℤ) * a = m * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1))
    (π : ↥(modularFunctionFieldC K N)) (hπ : x.ord π = 1)
    (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0) (hG : -a ≤ x.ord G) :
    x.evalAt (π ^ a * G) = 0 ↔ 1 ≤ stackOrd N m G x := by sorry
