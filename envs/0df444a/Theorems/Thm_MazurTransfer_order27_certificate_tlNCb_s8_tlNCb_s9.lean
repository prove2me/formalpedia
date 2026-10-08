-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s8_tlNCb_s9
-- name    : MazurTransfer.order27_certificate_tlNCb_s8_tlNCb_s9
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:21:44.193622+00:00
-- url     : https://prove2.me/theorems/0b7fd277-557e-42b7-b7d5-38862bf90282
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s8_tlNCb_s9
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s8, tlNCb_s9 identities in NumeratorCubeSteps8To15.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps8To15.lean, tlNCb_s8, tlNCb_s9. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s8_tlNCb_s9 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP8c0 f ξ + tlNCbP8c1 f ξ) + (tlNCbP8c2 f ξ + tlNCbP8c3 f ξ)) + ((tlNCbP8c4 f
        ξ + tlNCbP8c5 f ξ) + (tlNCbP8c6 f ξ + tlNCbP8c7 f ξ))) + ((tlNCbP8c8 f ξ +
        tlNCbP8c9 f ξ) + tlNCbP8c10 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP9c0 f ξ + tlNCbP9c1 f ξ) + (tlNCbP9c2 f ξ + tlNCbP9c3 f ξ)) + ((tlNCbP9c4 f
        ξ + tlNCbP9c5 f ξ) + (tlNCbP9c6 f ξ + tlNCbP9c7 f ξ))) + (((tlNCbP9c8 f ξ +
        tlNCbP9c9 f ξ) + (tlNCbP9c10 f ξ + tlNCbP9c11 f ξ)) + tlNCbP9c12 f ξ)) := by sorry
