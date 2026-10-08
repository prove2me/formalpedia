-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlTOne_s0_tlTOne_s1
-- name    : MazurTransfer.order27_certificate_tlTOne_s0_tlTOne_s1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:24:31.493183+00:00
-- url     : https://prove2.me/theorems/ff072cfd-4770-46c0-b8f1-7aff96432e68
-- title:
--   Order-27 polynomial reduction certificate: tlTOne_s0_tlTOne_s1
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlTOne_s0, tlTOne_s1 identities in TOneSteps0To4.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/TOneSteps0To4.lean, tlTOne_s0, tlTOne_s1. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlTOne_s0_tlTOne_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) +
        ((tlTOneP0c4 f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) +
        tlTOneP0c8 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP1c0 f ξ + tlTOneP1c1 f ξ) + (tlTOneP1c2 f ξ + tlTOneP1c3 f ξ)) +
        ((tlTOneP1c4 f ξ + tlTOneP1c5 f ξ) + (tlTOneP1c6 f ξ + tlTOneP1c7 f ξ))) +
        (tlTOneP1c8 f ξ + tlTOneP1c9 f ξ)) := by sorry
