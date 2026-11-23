-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_card_torsionBy
-- name    : GroundTheory.Arith.Abelian.card_torsionBy
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:57.425848+00:00
-- url     : https://prove2.me/theorems/6237175d-6c86-4d04-bf68-a2cd654c9807
-- title:
--   Abelian: card torsion By
-- statement:
--   The Abelian construction uses the card torsion By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean#L158-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean#L158-L164

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.card_torsionBy {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (torsionBy W.toAffine.Point n) = n ^ 2 := by sorry
