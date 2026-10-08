-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tl_band8_tl_band9
-- name    : MazurTransfer.order27_certificate_tl_band8_tl_band9
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:26:03.693654+00:00
-- url     : https://prove2.me/theorems/3f00cf48-4db6-46a0-8d8a-d5743a804a94
-- title:
--   Order-27 polynomial reduction certificate: tl_band8_tl_band9
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tl_band8, tl_band9 identities in Bands6To11.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/Bands6To11.lean, tl_band8, tl_band9. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tl_band8_tl_band9 :
  (∀ (f ξ : ℚ),
(((((tlNCbP0c8 f ξ + tlNCbP1c8 f ξ) + (tlNCbP2c8 f ξ + tlNCbP3c8 f ξ)) + ((tlNCbP4c8 f ξ +
      tlNCbP5c8 f ξ) + (tlNCbP6c7 f ξ + tlNCbP7c6 f ξ))) + (((tlNCbP8c8 f ξ + tlNCbP9c8 f ξ) +
      (tlNCbP10c8 f ξ + tlNCbP11c8 f ξ)) + ((tlNCbP12c8 f ξ + tlNCbP13c8 f ξ) + (tlNCbP14c7 f ξ +
      tlNCbP15c7 f ξ)))) + ((((tlNCbP16c6 f ξ + tlNCbP17c5 f ξ) + (tlNCbP18c8 f ξ + tlNCbP19c8 f
      ξ)) + ((tlNCbP20c8 f ξ + tlNCbP21c8 f ξ) + (tlNCbP22c8 f ξ + tlNCbP23c8 f ξ))) +
      (((tlNCbP24c7 f ξ + tlNCbP25c7 f ξ) + (tlNCbP26c6 f ξ + tlNCbP27c5 f ξ)) + ((tlNCbP28c4 f ξ
      + tlNCbP29c8 f ξ) + (tlNCbP30c8 f ξ + tlNCbP31c8 f ξ))))) + (((((tlNCbP32c8 f ξ + tlNCbP33c8
      f ξ) + (tlNCbP34c8 f ξ + tlNCbP35c7 f ξ)) + ((tlNCbP36c7 f ξ + tlNCbP37c6 f ξ) + (tlNCbP38c5
      f ξ + tlNCbP39c4 f ξ))) + (((tlNCbP40c3 f ξ + tlWTwoXP0c8 f ξ) + (tlWTwoXP1c8 f ξ +
      tlWTwoXP2c8 f ξ)) + ((tlWTwoXP3c8 f ξ + tlWOneXP0c8 f ξ) + (tlWOneXP1c8 f ξ + tlWOneXP2c8 f
      ξ)))) + (((tlWOneXP3c7 f ξ + tlWOneXP4c7 f ξ) + (tlWOneXP5c5 f ξ + tlWZeroXP0c8 f ξ)) +
      ((tlWZeroXP1c7 f ξ + tlWZeroXP2c5 f ξ) + tlWZeroXP3c0 f ξ))) = 0)
  ∧ (∀ (f ξ : ℚ),
(((((tlNCbP0c9 f ξ + tlNCbP1c9 f ξ) + (tlNCbP2c9 f ξ + tlNCbP3c9 f ξ)) + ((tlNCbP4c9 f ξ +
      tlNCbP5c9 f ξ) + (tlNCbP6c8 f ξ + tlNCbP7c7 f ξ))) + (((tlNCbP8c9 f ξ + tlNCbP9c9 f ξ) +
      (tlNCbP10c9 f ξ + tlNCbP11c9 f ξ)) + ((tlNCbP12c9 f ξ + tlNCbP13c9 f ξ) + (tlNCbP14c8 f ξ +
      tlNCbP15c8 f ξ)))) + ((((tlNCbP16c7 f ξ + tlNCbP17c6 f ξ) + (tlNCbP18c9 f ξ + tlNCbP19c9 f
      ξ)) + ((tlNCbP20c9 f ξ + tlNCbP21c9 f ξ) + (tlNCbP22c9 f ξ + tlNCbP23c9 f ξ))) +
      (((tlNCbP24c8 f ξ + tlNCbP25c8 f ξ) + (tlNCbP26c7 f ξ + tlNCbP27c6 f ξ)) + ((tlNCbP28c5 f ξ
      + tlNCbP29c9 f ξ) + (tlNCbP30c9 f ξ + tlNCbP31c9 f ξ))))) + (((((tlNCbP32c9 f ξ + tlNCbP33c9
      f ξ) + (tlNCbP34c9 f ξ + tlNCbP35c8 f ξ)) + ((tlNCbP36c8 f ξ + tlNCbP37c7 f ξ) + (tlNCbP38c6
      f ξ + tlNCbP39c5 f ξ))) + (((tlNCbP40c4 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP1c9 f ξ +
      tlWTwoXP2c9 f ξ)) + ((tlWTwoXP3c9 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP1c9 f ξ + tlWOneXP2c9 f
      ξ)))) + (((tlWOneXP3c8 f ξ + tlWOneXP4c8 f ξ) + (tlWOneXP5c6 f ξ + tlWZeroXP0c9 f ξ)) +
      ((tlWZeroXP1c8 f ξ + tlWZeroXP2c6 f ξ) + tlWZeroXP3c1 f ξ))) = 0) := by sorry
