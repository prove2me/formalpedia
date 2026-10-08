-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_zlTNSq_s1_zlTNSq_s2
-- name    : MazurTransfer.order27_certificate_zlTNSq_s1_zlTNSq_s2
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:26:30.127983+00:00
-- url     : https://prove2.me/theorems/5b3b4f22-47ca-46ba-b197-82d3f9ab1840
-- title:
--   Order-27 polynomial reduction certificate: zlTNSq_s1_zlTNSq_s2
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original zlTNSq_s1, zlTNSq_s2 identities in OrderTwentySevenLegStagesC.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesC.lean, zlTNSq_s1, zlTNSq_s2. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_zlTNSq_s1_zlTNSq_s2 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN1 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z)) + zlTNSqP1c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN2 f Z + zlTN3 Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP2c0 f Z + zlTNSqP2c1 f Z) + (zlTNSqP2c2 f Z + zlTNSqP2c3 f Z)) + zlTNSqP2c4
        f Z) := by sorry
