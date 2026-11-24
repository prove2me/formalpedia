-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_nonempty_torsionBy_addEquiv
-- name    : GroundTheory.Arith.Abelian.nonempty_torsionBy_addEquiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:45.273321+00:00
-- url     : https://prove2.me/theorems/40b44d17-e53d-42fd-ab94-2c4549df7f41
-- title:
--   Abelian: nonempty torsion By add Equiv
-- statement:
--   The Abelian construction uses the nonempty torsion By add Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean#L166-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean#L166-L185

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

theorem GroundTheory.Arith.Abelian.nonempty_torsionBy_addEquiv {n : ℕ} (hn : (n : F) ≠ 0) :
    Nonempty (torsionBy W.toAffine.Point n ≃+ ZMod n × ZMod n) := by sorry
