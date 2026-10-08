-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s0_tlTTwo_s1
-- name    : MazurTransfer.order27_certificate_tlTTwo_s0_tlTTwo_s1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:23:27.752981+00:00
-- url     : https://prove2.me/theorems/966925ad-7841-4780-865b-2bb7aa928f78
-- title:
--   Order-27 polynomial reduction certificate: tlTTwo_s0_tlTTwo_s1
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlTTwo_s0, tlTTwo_s1 identities in TTwoSteps0To6.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/TTwoSteps0To6.lean, tlTTwo_s0, tlTTwo_s1. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlTTwo_s0_tlTTwo_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c0 f ξ + tlNSqP0c1 f ξ + tlNSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) + (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) +
        ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ))) +
        (tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c3 f ξ + tlNSqP0c4 f ξ + tlNSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ) + (tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ)) +
        ((tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ) + (tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ))) +
        (((tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ) + (tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ)) +
        tlTTwoP1c12 f ξ)) := by sorry
