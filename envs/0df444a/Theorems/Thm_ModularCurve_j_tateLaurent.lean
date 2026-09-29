-- Prove2me | Theorems.Thm_ModularCurve_j_tateLaurent
-- name    : ModularCurve.j_tateLaurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/e9e36572-79dd-56a6-b28a-e4cac7f68ddd
-- title:
--   j-invariant of the formal Tate curve over K((q))
-- statement:
--   Let $K$ be a commutative ring. Consider the Weierstrass curve `tatePowerSeries` over $\mathbb{Z}[[q]]$ with coefficients $(a_1,a_2,a_3,a_4,a_6)=(1,0,0,\mathtt{tateA4},\mathtt{tateA6})$, and let `tateLaurent K` be its base change along `laurentOfInt K`, the ring homomorphism $\mathbb{Z}[[q]] \to K((q))$ obtained by reducing coefficients along $\mathbb{Z} \to K$ and then embedding power series into Laurent series (Hahn series over $\mathbb{Z}$ with values in $K$). The assertion is that the $j$-invariant of `tateLaurent K`, i.e. the product of the inverse of its discriminant, viewed as a unit of $K((q))$, with the cube of its $c_4$, equals `jqModC K`, which is by definition the Laurent series $\mathtt{single}(-1)(1) \cdot \iota(\mathtt{jNum}_K)$: the monomial $q^{-1}$ times the image in $K((q))$ of the power series `jNum` $= \mathtt{eisenstein4}^3 \cdot \mathtt{dedekindEtaUnitInv}$ with its integer coefficients read in $K$. No hypothesis on $K$ beyond commutativity is imposed; in particular no characteristic or integral-domain assumption.
--
--   This is the formal-series form of the defining property of the Tate curve: the curve with parameter $q$ has $j$-invariant the $q$-expansion $q^{-1}+744+196884q+\cdots$ of the modular function $j$. It is used, over various base rings, when matching Tate curves with points of modular curves, in particular in the constructions of variable changes and of points whose $j$-invariant is the expansion $j(q^N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_j_tateLaurent.lean

import Definitions.Def_ModularCurve_TateFormal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open PowerSeries HahnSeries ModularCurve

theorem ModularCurve.j_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).j = jqModC K := by sorry
