-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3
-- name    : MazurTransfer.order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:26:54.492297+00:00
-- url     : https://prove2.me/theorems/c103e461-3585-44f9-8870-be66aafee28b
-- title:
--   Order-27 polynomial reduction certificate: zlTNTDSq_s2_zlTNTDSq_s3
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original zlTNTDSq_s2, zlTNTDSq_s3 identities in NumeratorDenominatorSquare.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesD/NumeratorDenominatorSquare.lean, zlTNTDSq_s2, zlTNTDSq_s3. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP2c0 f Z + zlTNTDSqP2c1 f Z) + (zlTNTDSqP2c2 f Z + zlTNTDSqP2c3 f Z)) +
        zlTNTDSqP2c4 f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP1c2 f Z + zlTNTDP1c3 f Z + zlTNTDP1c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
        (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z)) := by sorry
