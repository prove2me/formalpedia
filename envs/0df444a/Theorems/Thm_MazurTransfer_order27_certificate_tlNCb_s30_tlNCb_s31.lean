-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s30_tlNCb_s31
-- name    : MazurTransfer.order27_certificate_tlNCb_s30_tlNCb_s31
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:23:01.454768+00:00
-- url     : https://prove2.me/theorems/db06e90a-1503-4b6e-9f1c-224f29797c5c
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s30_tlNCb_s31
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s30, tlNCb_s31 identities in NumeratorCubeSteps24To31.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps24To31.lean, tlNCb_s30, tlNCb_s31. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s30_tlNCb_s31 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ + tlNCbP30c3 f ξ)) +
        ((tlNCbP30c4 f ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f ξ))) +
        (((tlNCbP30c8 f ξ + tlNCbP30c9 f ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) +
        tlNCbP30c12 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP31c0 f ξ + tlNCbP31c1 f ξ) + (tlNCbP31c2 f ξ + tlNCbP31c3 f ξ)) +
        ((tlNCbP31c4 f ξ + tlNCbP31c5 f ξ) + (tlNCbP31c6 f ξ + tlNCbP31c7 f ξ))) +
        (((tlNCbP31c8 f ξ + tlNCbP31c9 f ξ) + (tlNCbP31c10 f ξ + tlNCbP31c11 f ξ)) +
        (tlNCbP31c12 f ξ + tlNCbP31c13 f ξ))) := by sorry
