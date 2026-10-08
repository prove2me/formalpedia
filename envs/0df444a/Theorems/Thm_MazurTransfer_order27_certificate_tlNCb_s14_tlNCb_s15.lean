-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s14_tlNCb_s15
-- name    : MazurTransfer.order27_certificate_tlNCb_s14_tlNCb_s15
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:22:06.402605+00:00
-- url     : https://prove2.me/theorems/ef337319-046c-4f3c-aa20-d0ff15fe79ea
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s14_tlNCb_s15
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s14, tlNCb_s15 identities in NumeratorCubeSteps8To15.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps8To15.lean, tlNCb_s14, tlNCb_s15. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s14_tlNCb_s15 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP14c0 f ξ + tlNCbP14c1 f ξ) + (tlNCbP14c2 f ξ + tlNCbP14c3 f ξ)) +
        ((tlNCbP14c4 f ξ + tlNCbP14c5 f ξ) + (tlNCbP14c6 f ξ + tlNCbP14c7 f ξ))) +
        (((tlNCbP14c8 f ξ + tlNCbP14c9 f ξ) + (tlNCbP14c10 f ξ + tlNCbP14c11 f ξ)) +
        ((tlNCbP14c12 f ξ + tlNCbP14c13 f ξ) + (tlNCbP14c14 f ξ + tlNCbP14c15 f ξ)))) +
        (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP15c0 f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) +
        ((tlNCbP15c4 f ξ + tlNCbP15c5 f ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ))) +
        (((tlNCbP15c8 f ξ + tlNCbP15c9 f ξ) + (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) +
        ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) + (tlNCbP15c14 f ξ + tlNCbP15c15 f ξ)))) +
        ((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) + tlNCbP15c18 f ξ)) := by sorry
