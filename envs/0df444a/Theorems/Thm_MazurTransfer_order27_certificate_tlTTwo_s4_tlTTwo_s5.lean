-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s4_tlTTwo_s5
-- name    : MazurTransfer.order27_certificate_tlTTwo_s4_tlTTwo_s5
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:23:33.82036+00:00
-- url     : https://prove2.me/theorems/444c7c7c-e936-43b6-990d-5ba3ad330783
-- title:
--   Order-27 polynomial reduction certificate: tlTTwo_s4_tlTTwo_s5
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlTTwo_s4, tlTTwo_s5 identities in TTwoSteps0To6.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/TTwoSteps0To6.lean, tlTTwo_s4, tlTTwo_s5. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlTTwo_s4_tlTTwo_s5 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c4 f ξ + tlNSqP1c5 f ξ + tlNSqP1c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ) + (tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ)) +
        ((tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ) + (tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ))) +
        (((tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ) + (tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ)) +
        (tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c7 f ξ + tlNSqP1c8 f ξ + tlNSqP1c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ) + (tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ)) +
        ((tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ) + (tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ))) +
        (((tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ) + (tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ)) +
        (tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ))) := by sorry
