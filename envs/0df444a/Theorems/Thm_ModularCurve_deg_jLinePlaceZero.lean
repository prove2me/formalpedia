-- Prove2me | Theorems.Thm_ModularCurve_deg_jLinePlaceZero
-- name    : ModularCurve.deg_jLinePlaceZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/6d6e0936-4104-597f-9f2e-43a465c2c9d8
-- title:
--   The place j=0 of the j-line has degree 1
-- statement:
--   The statement concerns the field $\mathbb{Q}\langle j\rangle$ obtained as the intermediate field generated over $\mathbb{Q}$ by the element `jq`, which is transcendental over $\mathbb{Q}$; for this field the project fixes the place [`ModularCurve.jLinePlaceZero`](def/ModularCurve_JLinePlaces.html#L54). Here a place of an extension $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and which is a principal ideal ring, and its degree is the $K$-dimension of the residue field of that local ring. The place in question is obtained by transporting, along the ring isomorphism [`ModularCurve.jLineRingEquiv : RatFunc ℚ ≃+* ℚ⟮jq⟯`](def/ModularCurve_JLinePlaces.html#L36) determined by the transcendence of `jq` (which sends the indeterminate to `jq` and is the identity on $\mathbb{Q}$), the place `placeOfPoint ℚ 0` of the rational function field $\mathbb{Q}(X)$, namely the finite place attached to the irreducible polynomial $X-0$; transport replaces the valuation subring by its preimage under the inverse isomorphism. The assertion is that the degree of this place equals $1$, i.e. its residue field is one-dimensional over $\mathbb{Q}$, so the place is rational.
--
--   This records that the point $j=0$ of the $j$-line is a rational point, the residue field being $\mathbb{Q}$ itself. It is used in the computation of ramification data for the covering of the $j$-line by the modular curve, entering the counts [`ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree`](thm.html#ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree) and [`ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo`](thm.html#ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo) of points above $j=0$ and $j=1728$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_jLinePlaceZero.lean

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve

theorem ModularCurve.deg_jLinePlaceZero : ModularCurve.jLinePlaceZero.deg = 1 := by sorry
