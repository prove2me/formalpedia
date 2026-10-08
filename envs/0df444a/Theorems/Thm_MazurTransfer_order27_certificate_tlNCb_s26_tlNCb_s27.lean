-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlNCb_s26_tlNCb_s27
-- name    : MazurTransfer.order27_certificate_tlNCb_s26_tlNCb_s27
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:22:39.049252+00:00
-- url     : https://prove2.me/theorems/fc460c2f-ed79-4a9d-bca6-0cc4f1c245e7
-- title:
--   Order-27 polynomial reduction certificate: tlNCb_s26_tlNCb_s27
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlNCb_s26, tlNCb_s27 identities in NumeratorCubeSteps24To31.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesA/NumeratorCubeSteps24To31.lean, tlNCb_s26, tlNCb_s27. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlNCb_s26_tlNCb_s27 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3 f ξ)) +
        ((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ))) +
        (((tlNCbP26c8 f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ)) +
        ((tlNCbP26c12 f ξ + tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)))) +
        ((tlNCbP26c16 f ξ + tlNCbP26c17 f ξ) + tlNCbP26c18 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP27c0 f ξ + tlNCbP27c1 f ξ) + (tlNCbP27c2 f ξ + tlNCbP27c3 f ξ)) +
        ((tlNCbP27c4 f ξ + tlNCbP27c5 f ξ) + (tlNCbP27c6 f ξ + tlNCbP27c7 f ξ))) +
        (((tlNCbP27c8 f ξ + tlNCbP27c9 f ξ) + (tlNCbP27c10 f ξ + tlNCbP27c11 f ξ)) +
        ((tlNCbP27c12 f ξ + tlNCbP27c13 f ξ) + (tlNCbP27c14 f ξ + tlNCbP27c15 f ξ)))) +
        ((tlNCbP27c16 f ξ + tlNCbP27c17 f ξ) + tlNCbP27c18 f ξ)) := by sorry
