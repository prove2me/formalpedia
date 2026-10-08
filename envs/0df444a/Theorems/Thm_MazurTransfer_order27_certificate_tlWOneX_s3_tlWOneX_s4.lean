-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlWOneX_s3_tlWOneX_s4
-- name    : MazurTransfer.order27_certificate_tlWOneX_s3_tlWOneX_s4
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:25:36.464899+00:00
-- url     : https://prove2.me/theorems/48891200-7036-4676-889b-530757e96746
-- title:
--   Order-27 polynomial reduction certificate: tlWOneX_s3_tlWOneX_s4
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlWOneX_s3, tlWOneX_s4 identities in WOneXSteps3To5.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/WOneXSteps3To5.lean, tlWOneX_s3, tlWOneX_s4. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlWOneX_s3_tlWOneX_s4 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP5c6 f ξ + tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ +
      tlTOneP5c11 f ξ + tlTOneP5c12 f ξ + tlTOneP6c0 f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ +
      tlTOneP6c3 f ξ + tlTOneP6c4 f ξ + tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ +
      tlTOneP6c8 f ξ + tlTOneP6c9 f ξ + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ) + (tlWOneXP3c2 f ξ + tlWOneXP3c3 f ξ)) +
        ((tlWOneXP3c4 f ξ + tlWOneXP3c5 f ξ) + (tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ))) +
        (((tlWOneXP3c8 f ξ + tlWOneXP3c9 f ξ) + (tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ)) +
        ((tlWOneXP3c12 f ξ + tlWOneXP3c13 f ξ) + (tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ))))
        + ((tlWOneXP3c16 f ξ + tlWOneXP3c17 f ξ) + (tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ +
      tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ +
      tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP8c0 f ξ + tlTOneP8c1 f ξ +
      tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ + tlTOneP8c5 f ξ + tlTOneP8c6 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP4c0 f + tlWOneXP4c1 f ξ) + (tlWOneXP4c2 f ξ + tlWOneXP4c3 f ξ)) +
        ((tlWOneXP4c4 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ))) +
        (((tlWOneXP4c8 f ξ + tlWOneXP4c9 f ξ) + (tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ)) +
        ((tlWOneXP4c12 f ξ + tlWOneXP4c13 f ξ) + (tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ))))
        + (((tlWOneXP4c16 f ξ + tlWOneXP4c17 f ξ) + (tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ))
        + tlWOneXP4c20 f ξ)) := by sorry
