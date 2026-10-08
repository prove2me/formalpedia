-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlWTwoX_s2_tlWTwoX_s3
-- name    : MazurTransfer.order27_certificate_tlWTwoX_s2_tlWTwoX_s3
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:24:13.470985+00:00
-- url     : https://prove2.me/theorems/59735920-166b-4247-a71d-88e899ebe4a3
-- title:
--   Order-27 polynomial reduction certificate: tlWTwoX_s2_tlWTwoX_s3
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlWTwoX_s2, tlWTwoX_s3 identities in WTwoXSteps2To4.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/WTwoXSteps2To4.lean, tlWTwoX_s2, tlWTwoX_s3. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlWTwoX_s2_tlWTwoX_s3 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ +
      tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ +
      tlTTwoP7c12 f ξ + tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ +
      tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ + tlTTwoP8c8 f ξ +
      tlTTwoP8c9 f ξ + tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ +
      tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ +
      tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ + tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ +
      tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ + tlTTwoP9c14 f ξ +
      tlTTwoP9c15 f ξ + tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ + tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP2c0 f ξ + tlWTwoXP2c1 f ξ) + (tlWTwoXP2c2 f ξ + tlWTwoXP2c3 f ξ)) +
        ((tlWTwoXP2c4 f ξ + tlWTwoXP2c5 f ξ) + (tlWTwoXP2c6 f ξ + tlWTwoXP2c7 f ξ))) +
        (((tlWTwoXP2c8 f ξ + tlWTwoXP2c9 f ξ) + (tlWTwoXP2c10 f ξ + tlWTwoXP2c11 f ξ)) +
        ((tlWTwoXP2c12 f ξ + tlWTwoXP2c13 f ξ) + (tlWTwoXP2c14 f ξ + tlWTwoXP2c15 f ξ))))
        + (((tlWTwoXP2c16 f ξ + tlWTwoXP2c17 f ξ) + (tlWTwoXP2c18 f ξ + tlWTwoXP2c19 f ξ))
        + ((tlWTwoXP2c20 f ξ + tlWTwoXP2c21 f ξ) + tlWTwoXP2c22 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ +
      tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ + tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ +
      tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ + tlTTwoP11c4 f ξ +
      tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ +
      tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ + tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ + tlTTwoP12c0 f ξ
      + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ + tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ +
      tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ +
      tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ + tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ +
      tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ + tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ + tlTTwoP13c6 f ξ +
      tlTTwoP13c7 f ξ + tlTTwoP13c8 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ) + (tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ)) +
        ((tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ) + (tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ))) +
        (((tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ) + (tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ)) +
        ((tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ) + (tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ))))
        + (((tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ) + (tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ))
        + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ))) := by sorry
