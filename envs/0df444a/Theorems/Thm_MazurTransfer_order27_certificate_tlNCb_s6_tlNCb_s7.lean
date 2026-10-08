-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s6_tlNCb_s7
-- name    : MazurTransfer.order27_certificate_tlNCb_s6_tlNCb_s7
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:21:47.68424+00:00
-- url     : https://prove2.me/theorems/590ad0d5-d29c-4d64-98bc-5ead8130d31d
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s6_tlNCb_s7
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s6, tlNCb_s7 identities in NumeratorCubeSteps0To7.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps0To7.lean, tlNCb_s6, tlNCb_s7. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s6_tlNCb_s7 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP6c0 f ξ + tlNCbP6c1 f ξ) + (tlNCbP6c2 f ξ + tlNCbP6c3 f ξ)) + ((tlNCbP6c4
        f ξ + tlNCbP6c5 f ξ) + (tlNCbP6c6 f ξ + tlNCbP6c7 f ξ))) + (((tlNCbP6c8 f ξ +
        tlNCbP6c9 f ξ) + (tlNCbP6c10 f ξ + tlNCbP6c11 f ξ)) + ((tlNCbP6c12 f ξ +
        tlNCbP6c13 f ξ) + (tlNCbP6c14 f ξ + tlNCbP6c15 f ξ)))) + (tlNCbP6c16 f ξ +
        tlNCbP6c17 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c7 f ξ + tlNSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ) + (tlNCbP7c2 f ξ + tlNCbP7c3 f ξ)) + ((tlNCbP7c4
        f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ + tlNCbP7c7 f ξ))) + (((tlNCbP7c8 f ξ +
        tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ)) + ((tlNCbP7c12 f ξ +
        tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)))) + ((tlNCbP7c16 f ξ +
        tlNCbP7c17 f ξ) + tlNCbP7c18 f ξ)) := by sorry
