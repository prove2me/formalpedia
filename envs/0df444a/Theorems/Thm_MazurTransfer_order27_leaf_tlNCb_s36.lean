-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s36
-- name    : MazurTransfer.order27_leaf_tlNCb_s36
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:38:48.878185+00:00
-- url     : https://prove2.me/theorems/f129279f-918b-43fa-856f-11987d7692c5
-- title:
--   Order-27 individual polynomial identity: tlNCb_s36
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNCb_s36 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps36To40, tlNCb_s36. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNCb_s36 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) +
        ((tlNCbP36c4 f ξ + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) +
        (((tlNCbP36c8 f ξ + tlNCbP36c9 f ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) +
        ((tlNCbP36c12 f ξ + tlNCbP36c13 f ξ) + (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) +
        ((tlNCbP36c16 f ξ + tlNCbP36c17 f ξ) + tlNCbP36c18 f ξ)) := by sorry
