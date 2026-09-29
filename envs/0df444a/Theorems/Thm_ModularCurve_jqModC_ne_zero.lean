-- Prove2me | Theorems.Thm_ModularCurve_jqModC_ne_zero
-- name    : ModularCurve.jqModC_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/7247999f-1d31-5a4a-ae9f-566d2109d582
-- title:
--   The q-expansion of j is nonzero over any nontrivial ring
-- statement:
--   Let $K$ be a type carrying a commutative ring structure which is in addition nontrivial (i.e. $0 \neq 1$ in $K$). Consider the Laurent series $\mathtt{jqModC}\ K \in K((q))$, realised as a Hahn series over $\mathbb{Z}$ with coefficients in $K$, defined as the product of the monomial `HahnSeries.single (-1) 1`, i.e. $q^{-1}$, with the image under `HahnSeries.ofPowerSeries` of the power series obtained from the integral series `jNum` $= E_4^3 \cdot \eta^{-24}$-type numerator (`eisenstein4 ^ 3 * dedekindEtaUnitInv` in $\mathbb{Z}[[q]]$) by applying the canonical ring homomorphism $\mathbb{Z} \to K$ coefficientwise. The assertion is that this element of $K((q))$ is not the zero series. No hypothesis beyond commutativity and nontriviality of $K$ is imposed; in particular $K$ need not be a field, and no characteristic assumption is made.
--
--   This records the basic nonvanishing of the reduction modulo an arbitrary nontrivial coefficient ring of the $q$-expansion $j(q) = q^{-1} + 744 + \cdots$ of the modular $j$-invariant, whose leading coefficient is $1$. It is the input to statements about the order of $\mathtt{jqModC}$ and to the computations of ramification indices of the inclusions of modular curves of level $H$ into curves of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jqModC_ne_zero.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.jqModC_ne_zero (K : Type*) [CommRing K] [Nontrivial K] :
    jqModC K ≠ 0 := by sorry
