-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s26
-- name    : MazurTransfer.order27_leaf_tlNCb_s26
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:37:34.821599+00:00
-- url     : https://prove2.me/theorems/e83f00ce-37a8-4aed-8242-1158bd419860
-- title:
--   Order-27 individual polynomial identity: tlNCb_s26
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNCb_s26 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps24To31, tlNCb_s26. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNCb_s26 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3 f ξ)) +
        ((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ))) +
        (((tlNCbP26c8 f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ)) +
        ((tlNCbP26c12 f ξ + tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)))) +
        ((tlNCbP26c16 f ξ + tlNCbP26c17 f ξ) + tlNCbP26c18 f ξ)) := by sorry
