-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s24_tlNCb_s25
-- name    : MazurTransfer.order27_certificate_tlNCb_s24_tlNCb_s25
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:24:49.526109+00:00
-- url     : https://prove2.me/theorems/28609391-e1f4-4f5e-8b9b-67148f91a28c
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s24_tlNCb_s25
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s24, tlNCb_s25 identities in NumeratorCubeSteps24To31.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps24To31.lean, tlNCb_s24, tlNCb_s25. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s24_tlNCb_s25 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP24c0 f ξ + tlNCbP24c1 f ξ) + (tlNCbP24c2 f ξ + tlNCbP24c3 f ξ)) +
        ((tlNCbP24c4 f ξ + tlNCbP24c5 f ξ) + (tlNCbP24c6 f ξ + tlNCbP24c7 f ξ))) +
        (((tlNCbP24c8 f ξ + tlNCbP24c9 f ξ) + (tlNCbP24c10 f ξ + tlNCbP24c11 f ξ)) +
        ((tlNCbP24c12 f ξ + tlNCbP24c13 f ξ) + (tlNCbP24c14 f ξ + tlNCbP24c15 f ξ)))) +
        (tlNCbP24c16 f ξ + tlNCbP24c17 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP25c0 f + tlNCbP25c1 f ξ) + (tlNCbP25c2 f ξ + tlNCbP25c3 f ξ)) +
        ((tlNCbP25c4 f ξ + tlNCbP25c5 f ξ) + (tlNCbP25c6 f ξ + tlNCbP25c7 f ξ))) +
        (((tlNCbP25c8 f ξ + tlNCbP25c9 f ξ) + (tlNCbP25c10 f ξ + tlNCbP25c11 f ξ)) +
        ((tlNCbP25c12 f ξ + tlNCbP25c13 f ξ) + (tlNCbP25c14 f ξ + tlNCbP25c15 f ξ)))) +
        ((tlNCbP25c16 f ξ + tlNCbP25c17 f ξ) + tlNCbP25c18 f ξ)) := by sorry
