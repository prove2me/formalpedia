-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_zlTNTD_s0_zlTNTD_s1
-- name    : MazurTransfer.order27_certificate_zlTNTD_s0_zlTNTD_s1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:26:47.03712+00:00
-- url     : https://prove2.me/theorems/491996a7-fcbc-463b-8a9c-476c01166e06
-- title:
--   Order-27 polynomial reduction certificate: zlTNTD_s0_zlTNTD_s1
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original zlTNTD_s0, zlTNTD_s1 identities in NumeratorDenominator.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesD/NumeratorDenominator.lean, zlTNTD_s0, zlTNTD_s1. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_zlTNTD_s0_zlTNTD_s1 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN0 f Z + zlTN1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + zlTNTDP0c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN2 f Z + zlTN3 Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) + (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z)) + zlTNTDP1c4
        f Z) := by sorry
