-- Prove2me | Theorems.Thm_MazurTransfer_order27_certificate_tlWTwoX_s0_tlWTwoX_s1
-- name    : MazurTransfer.order27_certificate_tlWTwoX_s0_tlWTwoX_s1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:24:08.524636+00:00
-- url     : https://prove2.me/theorems/a986bf6e-b918-49fe-9362-cecfb8f1a884
-- title:
--   Order-27 polynomial reduction certificate: tlWTwoX_s0_tlWTwoX_s1
-- statement:
--   This theorem packages the complete polynomial equalities specified below for rational values of the family parameter and the indicated coordinate. Each equality retains its stated vanishing-polynomial hypothesis, if any; every coefficient is fixed by the imported literal data. These are equality certificates modulo the trisection or kernel-cubic equation, not existence assertions. The named downstream consumer is the construction of the third rational hauptmodul leg in the unconditional order-27 exclusion. Formalization note: the package is precisely the conjunction of the fully quantified original tlWTwoX_s0, tlWTwoX_s1 identities in WTwoXSteps0To1.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenLegStagesB/WTwoXSteps0To1.lean, tlWTwoX_s0, tlWTwoX_s1. Complete original proof commands and Apache-2.0 header retained. Quantified statements assembled from Lean signature AST ranges.

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

theorem MazurTransfer.order27_certificate_tlWTwoX_s0_tlWTwoX_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
      tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ +
      tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ + tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ +
      tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ +
      tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ + tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ +
      tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ +
      tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ +
      tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ + tlTTwoP3c0 f ξ +
      tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ))))
        + (((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ))
        + tlWTwoXP0c20 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ +
      tlTTwoP3c11 f ξ + tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ +
      tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ +
      tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ +
      tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ +
      tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ +
      tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ + tlTTwoP6c0 f ξ +
      tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ +
      tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ + tlTTwoP7c0 f ξ +
      tlTTwoP7c1 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP1c0 f ξ + tlWTwoXP1c1 f ξ) + (tlWTwoXP1c2 f ξ + tlWTwoXP1c3 f ξ)) +
        ((tlWTwoXP1c4 f ξ + tlWTwoXP1c5 f ξ) + (tlWTwoXP1c6 f ξ + tlWTwoXP1c7 f ξ))) +
        (((tlWTwoXP1c8 f ξ + tlWTwoXP1c9 f ξ) + (tlWTwoXP1c10 f ξ + tlWTwoXP1c11 f ξ)) +
        ((tlWTwoXP1c12 f ξ + tlWTwoXP1c13 f ξ) + (tlWTwoXP1c14 f ξ + tlWTwoXP1c15 f ξ))))
        + (((tlWTwoXP1c16 f ξ + tlWTwoXP1c17 f ξ) + (tlWTwoXP1c18 f ξ + tlWTwoXP1c19 f ξ))
        + (tlWTwoXP1c20 f ξ + tlWTwoXP1c21 f ξ))) := by sorry
