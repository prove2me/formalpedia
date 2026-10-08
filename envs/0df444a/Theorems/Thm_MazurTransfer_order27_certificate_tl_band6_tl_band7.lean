-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tl_band6_tl_band7
-- name    : MazurTransfer.order27_certificate_tl_band6_tl_band7
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:25:51.779541+00:00
-- url     : https://prove2.me/theorems/24e9e96c-143e-42ce-b2db-76b7519111ed
-- title:
--   Order-27 polynomial reduction certificate: tl_band6_tl_band7
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tl_band6, tl_band7 identities in Bands6To11.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/Bands6To11.lean, tl_band6, tl_band7. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tl_band6_tl_band7 :
  (∀ (f ξ : ℚ),
(((((tlNCbP0c6 f ξ + tlNCbP1c6 f ξ) + (tlNCbP2c6 f ξ + tlNCbP3c6 f ξ)) + ((tlNCbP4c6 f ξ +
      tlNCbP5c6 f ξ) + (tlNCbP6c5 f ξ + tlNCbP7c4 f ξ))) + (((tlNCbP8c6 f ξ + tlNCbP9c6 f ξ) +
      (tlNCbP10c6 f ξ + tlNCbP11c6 f ξ)) + ((tlNCbP12c6 f ξ + tlNCbP13c6 f ξ) + (tlNCbP14c5 f ξ +
      tlNCbP15c5 f ξ)))) + ((((tlNCbP16c4 f ξ + tlNCbP17c3 f ξ) + (tlNCbP18c6 f ξ + tlNCbP19c6 f
      ξ)) + ((tlNCbP20c6 f ξ + tlNCbP21c6 f ξ) + (tlNCbP22c6 f ξ + tlNCbP23c6 f ξ))) +
      (((tlNCbP24c5 f ξ + tlNCbP25c5 f ξ) + (tlNCbP26c4 f ξ + tlNCbP27c3 f ξ)) + ((tlNCbP28c2 f ξ
      + tlNCbP29c6 f ξ) + (tlNCbP30c6 f ξ + tlNCbP31c6 f ξ))))) + (((((tlNCbP32c6 f ξ + tlNCbP33c6
      f ξ) + (tlNCbP34c6 f ξ + tlNCbP35c5 f ξ)) + ((tlNCbP36c5 f ξ + tlNCbP37c4 f ξ) + (tlNCbP38c3
      f ξ + tlNCbP39c2 f ξ))) + (((tlNCbP40c1 f ξ + tlWTwoXP0c6 f ξ) + (tlWTwoXP1c6 f ξ +
      tlWTwoXP2c6 f ξ)) + ((tlWTwoXP3c6 f ξ + tlWOneXP0c6 f ξ) + (tlWOneXP1c6 f ξ + tlWOneXP2c6 f
      ξ)))) + (((tlWOneXP3c5 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP5c3 f ξ + tlWZeroXP0c6 f ξ)) +
      (tlWZeroXP1c5 f ξ + tlWZeroXP2c3 f ξ))) = 0)
  ∧ (∀ (f ξ : ℚ),
(((((tlNCbP0c7 f ξ + tlNCbP1c7 f ξ) + (tlNCbP2c7 f ξ + tlNCbP3c7 f ξ)) + ((tlNCbP4c7 f ξ +
      tlNCbP5c7 f ξ) + (tlNCbP6c6 f ξ + tlNCbP7c5 f ξ))) + (((tlNCbP8c7 f ξ + tlNCbP9c7 f ξ) +
      (tlNCbP10c7 f ξ + tlNCbP11c7 f ξ)) + ((tlNCbP12c7 f ξ + tlNCbP13c7 f ξ) + (tlNCbP14c6 f ξ +
      tlNCbP15c6 f ξ)))) + ((((tlNCbP16c5 f ξ + tlNCbP17c4 f ξ) + (tlNCbP18c7 f ξ + tlNCbP19c7 f
      ξ)) + ((tlNCbP20c7 f ξ + tlNCbP21c7 f ξ) + (tlNCbP22c7 f ξ + tlNCbP23c7 f ξ))) +
      (((tlNCbP24c6 f ξ + tlNCbP25c6 f ξ) + (tlNCbP26c5 f ξ + tlNCbP27c4 f ξ)) + ((tlNCbP28c3 f ξ
      + tlNCbP29c7 f ξ) + (tlNCbP30c7 f ξ + tlNCbP31c7 f ξ))))) + (((((tlNCbP32c7 f ξ + tlNCbP33c7
      f ξ) + (tlNCbP34c7 f ξ + tlNCbP35c6 f ξ)) + ((tlNCbP36c6 f ξ + tlNCbP37c5 f ξ) + (tlNCbP38c4
      f ξ + tlNCbP39c3 f ξ))) + (((tlNCbP40c2 f ξ + tlWTwoXP0c7 f ξ) + (tlWTwoXP1c7 f ξ +
      tlWTwoXP2c7 f ξ)) + ((tlWTwoXP3c7 f ξ + tlWOneXP0c7 f ξ) + (tlWOneXP1c7 f ξ + tlWOneXP2c7 f
      ξ)))) + (((tlWOneXP3c6 f ξ + tlWOneXP4c6 f ξ) + (tlWOneXP5c4 f ξ + tlWZeroXP0c7 f ξ)) +
      (tlWZeroXP1c6 f ξ + tlWZeroXP2c4 f ξ))) = 0) := by sorry
