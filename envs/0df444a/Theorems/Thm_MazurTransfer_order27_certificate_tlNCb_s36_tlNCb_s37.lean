-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s36_tlNCb_s37
-- name    : MazurTransfer.order27_certificate_tlNCb_s36_tlNCb_s37
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:23:18.469002+00:00
-- url     : https://prove2.me/theorems/14c6e456-b5c7-4c60-93b7-b0502f9bfdf1
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s36_tlNCb_s37
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s36, tlNCb_s37 identities in NumeratorCubeSteps36To40.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps36To40.lean, tlNCb_s36, tlNCb_s37. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s36_tlNCb_s37 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) +
        ((tlNCbP36c4 f ξ + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) +
        (((tlNCbP36c8 f ξ + tlNCbP36c9 f ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) +
        ((tlNCbP36c12 f ξ + tlNCbP36c13 f ξ) + (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) +
        ((tlNCbP36c16 f ξ + tlNCbP36c17 f ξ) + tlNCbP36c18 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP37c0 f + tlNCbP37c1 f ξ) + (tlNCbP37c2 f ξ + tlNCbP37c3 f ξ)) +
        ((tlNCbP37c4 f ξ + tlNCbP37c5 f ξ) + (tlNCbP37c6 f ξ + tlNCbP37c7 f ξ))) +
        (((tlNCbP37c8 f ξ + tlNCbP37c9 f ξ) + (tlNCbP37c10 f ξ + tlNCbP37c11 f ξ)) +
        ((tlNCbP37c12 f ξ + tlNCbP37c13 f ξ) + (tlNCbP37c14 f ξ + tlNCbP37c15 f ξ)))) +
        ((tlNCbP37c16 f ξ + tlNCbP37c17 f ξ) + tlNCbP37c18 f ξ)) := by sorry
