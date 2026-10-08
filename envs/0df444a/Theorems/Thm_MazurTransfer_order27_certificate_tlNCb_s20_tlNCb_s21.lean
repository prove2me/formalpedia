-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s20_tlNCb_s21
-- name    : MazurTransfer.order27_certificate_tlNCb_s20_tlNCb_s21
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:22:25.252076+00:00
-- url     : https://prove2.me/theorems/d6fad867-0bc7-400d-9535-ffab8a5cfe98
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s20_tlNCb_s21
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s20, tlNCb_s21 identities in NumeratorCubeSteps16To23.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps16To23.lean, tlNCb_s20, tlNCb_s21. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s20_tlNCb_s21 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP20c0 f ξ + tlNCbP20c1 f ξ) + (tlNCbP20c2 f ξ + tlNCbP20c3 f ξ)) +
        ((tlNCbP20c4 f ξ + tlNCbP20c5 f ξ) + (tlNCbP20c6 f ξ + tlNCbP20c7 f ξ))) +
        (((tlNCbP20c8 f ξ + tlNCbP20c9 f ξ) + (tlNCbP20c10 f ξ + tlNCbP20c11 f ξ)) +
        (tlNCbP20c12 f ξ + tlNCbP20c13 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP21c0 f ξ + tlNCbP21c1 f ξ) + (tlNCbP21c2 f ξ + tlNCbP21c3 f ξ)) +
        ((tlNCbP21c4 f ξ + tlNCbP21c5 f ξ) + (tlNCbP21c6 f ξ + tlNCbP21c7 f ξ))) +
        (((tlNCbP21c8 f ξ + tlNCbP21c9 f ξ) + (tlNCbP21c10 f ξ + tlNCbP21c11 f ξ)) +
        ((tlNCbP21c12 f ξ + tlNCbP21c13 f ξ) + tlNCbP21c14 f ξ))) := by sorry
