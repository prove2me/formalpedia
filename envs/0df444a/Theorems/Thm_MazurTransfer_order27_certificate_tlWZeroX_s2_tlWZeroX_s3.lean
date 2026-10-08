-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlWZeroX_s2_tlWZeroX_s3
-- name    : MazurTransfer.order27_certificate_tlWZeroX_s2_tlWZeroX_s3
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:25:42.796749+00:00
-- url     : https://prove2.me/theorems/779fc503-3a47-4198-ba59-11af2f08a224
-- title:
--   Order-27 polynomial reduction certificate: tlWZeroX_s2_tlWZeroX_s3
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlWZeroX_s2, tlWZeroX_s3 identities in WZeroXSteps.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/WZeroXSteps.lean, tlWZeroX_s2, tlWZeroX_s3. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlWZeroX_s2_tlWZeroX_s3 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP2c3 f ξ + tlDCbP2c4 f ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ + tlDCbP2c8 f ξ
      + tlDCbP2c9 f ξ + tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ + tlDCbP2c13 f ξ +
      tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ)) +
        ((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ))) +
        (((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ))
        + ((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f
        ξ)))) + ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ +
        tlWZeroXP2c19 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP3c2 f ξ + tlDCbP3c3 f ξ + tlDCbP3c4 f ξ + tlDCbP3c5 f ξ + tlDCbP3c6 f ξ + tlDCbP3c7 f ξ
      + tlDCbP3c8 f ξ + tlDCbP3c9 f ξ + tlDCbP3c10 f ξ + tlDCbP3c11 f ξ) * tlMZeroV0 f =
      (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ))
        + ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f
        ξ)))) := by sorry
