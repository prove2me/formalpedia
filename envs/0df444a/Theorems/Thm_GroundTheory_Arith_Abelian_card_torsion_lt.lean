-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_card_torsion_lt
-- name    : GroundTheory.Arith.Abelian.card_torsion_lt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:17.705407+00:00
-- url     : https://prove2.me/theorems/c2dd49e3-fb5e-4879-948d-d0ae3dd713ed
-- title:
--   Abelian: card torsion lt
-- statement:
--   The Abelian construction uses the card torsion lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L127-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L127-L143

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]

theorem GroundTheory.Arith.Abelian.card_torsion_lt : Nat.card {P : E.toAffine.Point // (p : ℤ) • P = 0} < p ^ 2 := by sorry
