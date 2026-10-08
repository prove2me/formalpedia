-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s22_tlNCb_s23
-- name    : MazurTransfer.order27_certificate_tlNCb_s22_tlNCb_s23
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:22:28.286493+00:00
-- url     : https://prove2.me/theorems/867de889-b6f2-497b-89fd-07b4f47c4e9b
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s22_tlNCb_s23
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s22, tlNCb_s23 identities in NumeratorCubeSteps16To23.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps16To23.lean, tlNCb_s22, tlNCb_s23. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s22_tlNCb_s23 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP22c0 f ξ + tlNCbP22c1 f ξ) + (tlNCbP22c2 f ξ + tlNCbP22c3 f ξ)) +
        ((tlNCbP22c4 f ξ + tlNCbP22c5 f ξ) + (tlNCbP22c6 f ξ + tlNCbP22c7 f ξ))) +
        (((tlNCbP22c8 f ξ + tlNCbP22c9 f ξ) + (tlNCbP22c10 f ξ + tlNCbP22c11 f ξ)) +
        ((tlNCbP22c12 f ξ + tlNCbP22c13 f ξ) + (tlNCbP22c14 f ξ + tlNCbP22c15 f ξ))))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP23c0 f ξ + tlNCbP23c1 f ξ) + (tlNCbP23c2 f ξ + tlNCbP23c3 f ξ)) +
        ((tlNCbP23c4 f ξ + tlNCbP23c5 f ξ) + (tlNCbP23c6 f ξ + tlNCbP23c7 f ξ))) +
        (((tlNCbP23c8 f ξ + tlNCbP23c9 f ξ) + (tlNCbP23c10 f ξ + tlNCbP23c11 f ξ)) +
        ((tlNCbP23c12 f ξ + tlNCbP23c13 f ξ) + (tlNCbP23c14 f ξ + tlNCbP23c15 f ξ)))) +
        tlNCbP23c16 f ξ) := by sorry
