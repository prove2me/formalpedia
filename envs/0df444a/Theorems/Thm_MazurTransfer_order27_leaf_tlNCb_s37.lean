-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s37
-- name    : MazurTransfer.order27_leaf_tlNCb_s37
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:40:36.117912+00:00
-- url     : https://prove2.me/theorems/59cf4fbd-8f7f-4d0e-b3eb-586f3b92c646
-- title:
--   Order-27 individual polynomial identity: tlNCb_s37
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNCb_s37 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps36To40, tlNCb_s37. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNCb_s37 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP37c0 f + tlNCbP37c1 f ξ) + (tlNCbP37c2 f ξ + tlNCbP37c3 f ξ)) +
        ((tlNCbP37c4 f ξ + tlNCbP37c5 f ξ) + (tlNCbP37c6 f ξ + tlNCbP37c7 f ξ))) +
        (((tlNCbP37c8 f ξ + tlNCbP37c9 f ξ) + (tlNCbP37c10 f ξ + tlNCbP37c11 f ξ)) +
        ((tlNCbP37c12 f ξ + tlNCbP37c13 f ξ) + (tlNCbP37c14 f ξ + tlNCbP37c15 f ξ)))) +
        ((tlNCbP37c16 f ξ + tlNCbP37c17 f ξ) + tlNCbP37c18 f ξ)) := by sorry
