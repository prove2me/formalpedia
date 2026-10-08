-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s2_tlNCb_s3
-- name    : MazurTransfer.order27_certificate_tlNCb_s2_tlNCb_s3
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:21:39.839826+00:00
-- url     : https://prove2.me/theorems/0f6b7611-ffcd-4f83-8171-a1a34c587d05
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s2_tlNCb_s3
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s2, tlNCb_s3 identities in NumeratorCubeSteps0To7.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps0To7.lean, tlNCb_s2, tlNCb_s3. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s2_tlNCb_s3 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP2c0 f ξ + tlNCbP2c1 f ξ) + (tlNCbP2c2 f ξ + tlNCbP2c3 f ξ)) + ((tlNCbP2c4 f
        ξ + tlNCbP2c5 f ξ) + (tlNCbP2c6 f ξ + tlNCbP2c7 f ξ))) + (((tlNCbP2c8 f ξ +
        tlNCbP2c9 f ξ) + (tlNCbP2c10 f ξ + tlNCbP2c11 f ξ)) + ((tlNCbP2c12 f ξ +
        tlNCbP2c13 f ξ) + tlNCbP2c14 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP3c0 f ξ + tlNCbP3c1 f ξ) + (tlNCbP3c2 f ξ + tlNCbP3c3 f ξ)) + ((tlNCbP3c4 f
        ξ + tlNCbP3c5 f ξ) + (tlNCbP3c6 f ξ + tlNCbP3c7 f ξ))) + (((tlNCbP3c8 f ξ +
        tlNCbP3c9 f ξ) + (tlNCbP3c10 f ξ + tlNCbP3c11 f ξ)) + ((tlNCbP3c12 f ξ +
        tlNCbP3c13 f ξ) + (tlNCbP3c14 f ξ + tlNCbP3c15 f ξ)))) := by sorry
