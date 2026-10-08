-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s0
-- name    : MazurTransfer.order27_leaf_tlNCb_s0
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:32:02.046185+00:00
-- url     : https://prove2.me/theorems/d68f6442-fe4b-4554-b151-37d8537e0ccc
-- title:
--   Order-27 individual polynomial identity: tlNCb_s0
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNCb_s0 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps0To7, tlNCb_s0. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNCb_s0 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP0c0 f ξ + tlNCbP0c1 f ξ) + (tlNCbP0c2 f ξ + tlNCbP0c3 f ξ)) + ((tlNCbP0c4 f
        ξ + tlNCbP0c5 f ξ) + (tlNCbP0c6 f ξ + tlNCbP0c7 f ξ))) + ((tlNCbP0c8 f ξ +
        tlNCbP0c9 f ξ) + tlNCbP0c10 f ξ)) := by sorry
