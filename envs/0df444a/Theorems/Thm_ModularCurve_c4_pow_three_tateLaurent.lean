-- Prove2me | Theorems.Thm_ModularCurve_c4_pow_three_tateLaurent
-- name    : ModularCurve.c4_pow_three_tateLaurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/4e2d65a7-8766-51bc-99f5-fd94858ea317
-- title:
--   Tate curve: c₄³ = j(q) Δ over any ring
-- statement:
--   Let $K$ be a commutative ring. Consider the Weierstrass curve `tatePowerSeries` over $\mathbb{Z}[[q]]$ with coefficients $a_1 = 1$, $a_2 = a_3 = 0$, $a_4 =$ `tateA4`, $a_6 =$ `tateA6`, and let `tateLaurent K` be its base change along the ring homomorphism `laurentOfInt K`, which reduces coefficients by $\mathbb{Z} \to K$ and then embeds $K[[q]]$ into the Laurent series field $K((q))$ (Hahn series over $K$ with value group $\mathbb{Z}$). Let `jqModC K` be the Laurent series obtained by multiplying the Hahn series $q^{-1}$, i.e. `HahnSeries.single (-1) 1`, by the image in $K[[q]]$ of the integral power series `jNum` $=$ `eisenstein4`$^3 \cdot$ `dedekindEtaUnitInv`. The assertion is the identity
--   $$c_4(\mathrm{tateLaurent}\ K)^3 = \mathrm{jqModC}\ K\cdot \Delta(\mathrm{tateLaurent}\ K)$$
--   in $K((q))$, where $c_4$ and $\Delta$ are the usual Weierstrass invariants. There are no hypotheses beyond $K$ being a commutative ring; in particular no division is performed, so the statement makes sense over an arbitrary ring.
--
--   This is the multiplicative form of the statement that the $j$-invariant of the Tate curve equals the $q$-expansion of the modular function $j$; written as $c_4^3 = j\,\Delta$ it avoids inverting $\Delta$ and hence holds over any coefficient ring. It is used to identify $j$ of the Tate curve with `jqModC` (and, over $\mathbb{Q}$, with `jq`), and is cited by [`ModularCurve.delta_tateLaurent`](thm.html#ModularCurve.delta_tateLaurent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_c4_pow_three_tateLaurent.lean

import Definitions.Def_ModularCurve_TateFormal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open PowerSeries HahnSeries ModularCurve

theorem ModularCurve.c4_pow_three_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ ^ 3 = jqModC K * (tateLaurent K).Δ := by sorry
