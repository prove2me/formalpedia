-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_zlTNCb_s0_zlTNSqTD_s0
-- name    : MazurTransfer.order27_certificate_zlTNCb_s0_zlTNSqTD_s0
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:26:20.892182+00:00
-- url     : https://prove2.me/theorems/8db95eaa-4ce9-49d6-adcf-a01c7249d3e0
-- title:
--   Order-27 polynomial reduction certificate: zlTNCb_s0_zlTNSqTD_s0
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original zlTNCb_s0, zlTNSqTD_s0 identities in OrderTwentySevenLegStagesC.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesC.lean, zlTNCb_s0, zlTNSqTD_s0. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_zlTNCb_s0_zlTNSqTD_s0 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN0 f Z + zlTN1 f Z + zlTN2 f Z + zlTN3 Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z))) := by sorry
