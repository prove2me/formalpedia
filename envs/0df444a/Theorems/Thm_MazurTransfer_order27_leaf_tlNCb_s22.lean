-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s22
-- name    : MazurTransfer.order27_leaf_tlNCb_s22
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:36:01.774151+00:00
-- url     : https://prove2.me/theorems/8403741e-b4d0-429f-bf3e-ea5bb683619e
-- title:
--   Order-27 individual polynomial identity: tlNCb_s22
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNCb_s22 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorCubeSteps16To23, tlNCb_s22. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNCb_s22 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP22c0 f ξ + tlNCbP22c1 f ξ) + (tlNCbP22c2 f ξ + tlNCbP22c3 f ξ)) +
        ((tlNCbP22c4 f ξ + tlNCbP22c5 f ξ) + (tlNCbP22c6 f ξ + tlNCbP22c7 f ξ))) +
        (((tlNCbP22c8 f ξ + tlNCbP22c9 f ξ) + (tlNCbP22c10 f ξ + tlNCbP22c11 f ξ)) +
        ((tlNCbP22c12 f ξ + tlNCbP22c13 f ξ) + (tlNCbP22c14 f ξ + tlNCbP22c15 f ξ)))) := by sorry
