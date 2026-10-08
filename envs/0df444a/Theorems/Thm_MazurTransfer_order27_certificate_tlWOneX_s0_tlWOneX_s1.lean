-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlWOneX_s0_tlWOneX_s1
-- name    : MazurTransfer.order27_certificate_tlWOneX_s0_tlWOneX_s1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:25:07.470824+00:00
-- url     : https://prove2.me/theorems/1519dfb4-a9e1-44e1-904e-e4cce47b21a0
-- title:
--   Order-27 polynomial reduction certificate: tlWOneX_s0_tlWOneX_s1
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlWOneX_s0, tlWOneX_s1 identities in WOneXSteps0To2.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/WOneXSteps0To2.lean, tlWOneX_s0, tlWOneX_s1. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlWOneX_s0_tlWOneX_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
      tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP1c0 f ξ +
      tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ + tlTOneP1c5 f ξ +
      tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ + tlTOneP2c0 f ξ +
      tlTOneP2c1 f ξ) * tlMOneV0 f =
      (((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + tlWOneXP0c14 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP2c2 f ξ + tlTOneP2c3 f ξ + tlTOneP2c4 f ξ + tlTOneP2c5 f ξ + tlTOneP2c6 f ξ +
      tlTOneP2c7 f ξ + tlTOneP2c8 f ξ + tlTOneP2c9 f ξ + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ +
      tlTOneP3c0 f ξ + tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ +
      tlTOneP3c5 f ξ + tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ +
      tlTOneP3c10 f ξ) * tlMOneV0 f =
      ((((tlWOneXP1c0 f ξ + tlWOneXP1c1 f ξ) + (tlWOneXP1c2 f ξ + tlWOneXP1c3 f ξ)) +
        ((tlWOneXP1c4 f ξ + tlWOneXP1c5 f ξ) + (tlWOneXP1c6 f ξ + tlWOneXP1c7 f ξ))) +
        (((tlWOneXP1c8 f ξ + tlWOneXP1c9 f ξ) + (tlWOneXP1c10 f ξ + tlWOneXP1c11 f ξ)) +
        ((tlWOneXP1c12 f ξ + tlWOneXP1c13 f ξ) + (tlWOneXP1c14 f ξ + tlWOneXP1c15 f ξ))))
        + tlWOneXP1c16 f ξ) := by sorry
