-- Prove2me | Theorems.Thm_MazurTransfer_order27_third_leg_polynomial
-- name    : MazurTransfer.order27_third_leg_polynomial
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:38:34.843764+00:00
-- url     : https://prove2.me/theorems/efd9a47c-2c93-4936-a2ad-ec1e6eff5ad7
-- title:
--   The kernel-cubic coordinate satisfies the third-leg polynomial identity
-- statement:
--   Put $A(f)=(f^3-6f^2+3f+1)^3$, $B(f)=f(f-1)(f^2-f+1)^3$, and let $U(f,Z)$ and $E(f,Z)$ be the fixed imported numerator and denominator polynomials for the third leg. If $f,Z\in\mathbb Q$ satisfy the imported kernel-cubic equation $M(f,Z)=0$, then $$A^2BU^3+(36A^2B+729AB^2)U^2E^2+(270A^2B+26244AB^2+531441B^3)UE^4-A^3E^6=0.$$ Every symbol in this formula is evaluated at the displayed arguments. The downstream third-leg construction separately proves $B\ne0$ and $E\ne0$, then clears denominators to obtain the Fricke-twisted $X_0(9)$ correspondence. This polynomial identity itself needs only $M(f,Z)=0$.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.BigIdentity, zl_big. Full signature extracted from Lean AST ranges. Original aggregation and regularity proofs retained; expensive primitive identities use exact public certificates.

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_third_leg_polynomial {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * ((zlTN0 f Z +
      zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) ^ 3 + (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f *
      (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) *
      (f ^ 2 - f + 1) ^ 3) ^ 2) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) ^ 2 * zlE0 f Z
      ^ 2 + (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) +
      26244 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 +
      531441 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z +
      zlTN3 Z)) * zlE0 f Z ^ 4 + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) * zlE0 f Z ^ 6 = 0  := by sorry
