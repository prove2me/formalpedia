-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s1
-- name    : MazurTransfer.order27_leaf_tlTTwo_s1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:39:35.436069+00:00
-- url     : https://prove2.me/theorems/4f6684be-6bb0-4a34-b0ed-69139483f703
-- title:
--   Order-27 individual polynomial identity: tlTTwo_s1
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlTTwo_s1 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps0To6, tlTTwo_s1. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlTTwo_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c3 f ξ + tlNSqP0c4 f ξ + tlNSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ) + (tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ)) +
        ((tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ) + (tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ))) +
        (((tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ) + (tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ)) +
        tlTTwoP1c12 f ξ)) := by sorry
