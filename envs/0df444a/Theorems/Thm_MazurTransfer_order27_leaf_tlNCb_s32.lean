-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s32
-- name    : MazurTransfer.order27_leaf_tlNCb_s32
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:38:49.819169+00:00
-- url     : https://prove2.me/theorems/91eaa532-83fc-4f2f-b790-1a0632d88945
-- title:
--   Order-27 individual polynomial identity: tlNCb_s32
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNCb_s32 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps32To35, tlNCb_s32. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNCb_s32 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP32c0 f ξ + tlNCbP32c1 f ξ) + (tlNCbP32c2 f ξ + tlNCbP32c3 f ξ)) +
        ((tlNCbP32c4 f ξ + tlNCbP32c5 f ξ) + (tlNCbP32c6 f ξ + tlNCbP32c7 f ξ))) +
        (((tlNCbP32c8 f ξ + tlNCbP32c9 f ξ) + (tlNCbP32c10 f ξ + tlNCbP32c11 f ξ)) +
        ((tlNCbP32c12 f ξ + tlNCbP32c13 f ξ) + (tlNCbP32c14 f ξ + tlNCbP32c15 f ξ)))) := by sorry
