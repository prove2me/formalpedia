-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_zlTDSq_s0_zlTDCb_s0
-- name    : MazurTransfer.order27_certificate_zlTDSq_s0_zlTDCb_s0
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:26:14.662261+00:00
-- url     : https://prove2.me/theorems/da31338f-dcf6-4990-acb4-bd760fbe8749
-- title:
--   Order-27 polynomial reduction certificate: zlTDSq_s0_zlTDCb_s0
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original zlTDSq_s0, zlTDCb_s0 identities in DenominatorPowers.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesD/DenominatorPowers.lean, zlTDSq_s0, zlTDCb_s0. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_zlTDSq_s0_zlTDCb_s0 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
      =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + zlTDCbP0c4
        f Z) := by sorry
