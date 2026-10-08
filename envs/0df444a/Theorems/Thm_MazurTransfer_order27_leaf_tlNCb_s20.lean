-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s20
-- name    : MazurTransfer.order27_leaf_tlNCb_s20
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:34:06.872513+00:00
-- url     : https://prove2.me/theorems/98d861f0-36f5-4546-940a-e5aec7ddc325
-- title:
--   Order-27 individual polynomial identity: tlNCb_s20
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNCb_s20 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps16To23, tlNCb_s20. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNCb_s20 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP20c0 f ξ + tlNCbP20c1 f ξ) + (tlNCbP20c2 f ξ + tlNCbP20c3 f ξ)) +
        ((tlNCbP20c4 f ξ + tlNCbP20c5 f ξ) + (tlNCbP20c6 f ξ + tlNCbP20c7 f ξ))) +
        (((tlNCbP20c8 f ξ + tlNCbP20c9 f ξ) + (tlNCbP20c10 f ξ + tlNCbP20c11 f ξ)) +
        (tlNCbP20c12 f ξ + tlNCbP20c13 f ξ))) := by sorry
