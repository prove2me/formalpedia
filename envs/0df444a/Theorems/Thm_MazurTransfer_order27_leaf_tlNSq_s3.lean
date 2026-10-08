-- Prove2me | Theorems.Thm_MazurTransfer_order27_leaf_tlNSq_s3
-- name    : MazurTransfer.order27_leaf_tlNSq_s3
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:28:43.16625+00:00
-- url     : https://prove2.me/theorems/abd231f1-cebc-40da-9d59-cb2837ce0a0d
-- title:
--   Order-27 individual polynomial identity: tlNSq_s3
-- statement:
--   For every rational family parameter and coordinate satisfying the displayed vanishing equation, the specified product equals the full sum of the fixed polynomial remainder chunks. This is the complete original tlNSq_s3 identity. Its downstream consumer reconstructs the original paired certificate and then the third hauptmodul leg; no existence or torsion assertion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorSquare, tlNSq_s3. Complete statement and proof selected using original Lean AST ranges. Split after the paired server proof reached its verification limit; no mathematical type changed.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert

theorem MazurTransfer.order27_leaf_tlNSq_s3 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlN3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP3c0 f ξ + tlNSqP3c1 f ξ) + (tlNSqP3c2 f ξ + tlNSqP3c3 f ξ)) + ((tlNSqP3c4 f
        ξ + tlNSqP3c5 f ξ) + (tlNSqP3c6 f ξ + tlNSqP3c7 f ξ))) + ((tlNSqP3c8 f ξ +
        tlNSqP3c9 f ξ) + (tlNSqP3c10 f ξ + tlNSqP3c11 f ξ))) := by sorry
