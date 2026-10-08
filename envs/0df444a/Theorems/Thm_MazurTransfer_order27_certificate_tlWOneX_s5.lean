-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlWOneX_s5
-- name    : MazurTransfer.order27_certificate_tlWOneX_s5
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:25:20.656584+00:00
-- url     : https://prove2.me/theorems/87c528db-e594-4661-84aa-5dcf9c37713c
-- title:
--   Order-27 polynomial reduction certificate: tlWOneX_s5
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlWOneX_s5 identities in WOneXSteps3To5.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/WOneXSteps3To5.lean, tlWOneX_s5. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlWOneX_s5 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ +
      tlTOneP8c12 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ + tlTOneP9c3 f ξ +
      tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ + tlTOneP9c8 f ξ +
      tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ) * tlMOneV0 f =
      ((((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ)) +
        ((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ))) +
        (((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ)) +
        ((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ))))
        + (((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ))
        + tlWOneXP5c20 f ξ)) := by sorry
