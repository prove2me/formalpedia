-- Prove2me | Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
-- name    : ModularCurve.coeff_jqModC_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/04648caf-af88-5da0-a32d-39381fd62321
-- title:
--   The q⁻¹ coefficient of ̄ j is 1
-- statement:
--   Let $K$ be a commutative ring. The Laurent series $\bar j =$ `jqModC K` $\in K((q))$ is by definition the product of the Hahn series `HahnSeries.single (-1) 1`, i.e. the monomial $q^{-1}$ with coefficient $1$, with the image in $K((q))$ of the power series obtained from the integral power series `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv` $\in \mathbb{Z}[[q]]$ by applying the ring homomorphism $\mathbb{Z} \to K$ coefficientwise and then including $K[[q]]$ into $K((q))$. The theorem asserts that the coefficient of this Laurent series at the exponent $-1 \in \mathbb{Z}$ equals $1$ in $K$. No hypotheses beyond the commutative ring structure on $K$ are imposed; in particular $K$ may be trivial, in which case the assertion is vacuous, and $K$ may have any characteristic.
--
--   This records the leading behaviour of the $q$-expansion $j = q^{-1} + 744 + \cdots$ after reduction of coefficients into an arbitrary commutative ring: the pole at the cusp has exact order one and normalised leading coefficient. It is the normalisation used throughout the treatment of $q$-expansions on $X_0(N)$ and of mod $p$ modular forms, and is invoked, among other places, in the identification of functions in the mod $p$ form and cusp form modules via their $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_jqModC_neg_one.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_jqModC_neg_one (K : Type*) [CommRing K] :
    (jqModC K).coeff (-1 : ℤ) = 1 := by sorry
