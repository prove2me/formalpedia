-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s13
-- name    : MazurTransfer.order27_leaf_tlTTwo_s13
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:47:12.028513+00:00
-- url     : https://prove2.me/theorems/612e4504-184c-4b7c-8e64-307dc691a6d5
-- title:
--   Order-27 individual polynomial identity: tlTTwo_s13
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlTTwo_s13 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps10To13, tlTTwo_s13. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlTTwo_s13 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c10 f ξ + tlNSqP3c11 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ) + (tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ)) +
        ((tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ) + (tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ))) +
        (((tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ) + (tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ)) +
        tlTTwoP13c12 f ξ)) := by sorry
