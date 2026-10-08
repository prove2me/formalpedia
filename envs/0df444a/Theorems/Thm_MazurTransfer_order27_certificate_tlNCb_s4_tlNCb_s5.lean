-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s4_tlNCb_s5
-- name    : MazurTransfer.order27_certificate_tlNCb_s4_tlNCb_s5
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:21:30.722271+00:00
-- url     : https://prove2.me/theorems/0365dab5-bd38-4c88-9b80-6156e83da8ed
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s4_tlNCb_s5
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s4, tlNCb_s5 identities in NumeratorCubeSteps0To7.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps0To7.lean, tlNCb_s4, tlNCb_s5. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s4_tlNCb_s5 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP4c0 f ξ + tlNCbP4c1 f ξ) + (tlNCbP4c2 f ξ + tlNCbP4c3 f ξ)) + ((tlNCbP4c4
        f ξ + tlNCbP4c5 f ξ) + (tlNCbP4c6 f ξ + tlNCbP4c7 f ξ))) + (((tlNCbP4c8 f ξ +
        tlNCbP4c9 f ξ) + (tlNCbP4c10 f ξ + tlNCbP4c11 f ξ)) + ((tlNCbP4c12 f ξ +
        tlNCbP4c13 f ξ) + (tlNCbP4c14 f ξ + tlNCbP4c15 f ξ)))) + tlNCbP4c16 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP5c0 f ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f ξ + tlNCbP5c3 f ξ)) + ((tlNCbP5c4
        f ξ + tlNCbP5c5 f ξ) + (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ))) + (((tlNCbP5c8 f ξ +
        tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ + tlNCbP5c11 f ξ)) + ((tlNCbP5c12 f ξ +
        tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f ξ)))) + (tlNCbP5c16 f ξ +
        tlNCbP5c17 f ξ)) := by sorry
