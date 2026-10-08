-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s10
-- name    : MazurTransfer.order27_leaf_tlNCb_s10
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:32:17.545409+00:00
-- url     : https://prove2.me/theorems/a283c2ed-93a3-4ebd-8a29-e206bcf9cfff
-- title:
--   Order-27 individual polynomial identity: tlNCb_s10
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNCb_s10 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps8To15, tlNCb_s10. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNCb_s10 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP10c0 f ξ + tlNCbP10c1 f ξ) + (tlNCbP10c2 f ξ + tlNCbP10c3 f ξ)) +
        ((tlNCbP10c4 f ξ + tlNCbP10c5 f ξ) + (tlNCbP10c6 f ξ + tlNCbP10c7 f ξ))) +
        (((tlNCbP10c8 f ξ + tlNCbP10c9 f ξ) + (tlNCbP10c10 f ξ + tlNCbP10c11 f ξ)) +
        (tlNCbP10c12 f ξ + tlNCbP10c13 f ξ))) := by sorry
