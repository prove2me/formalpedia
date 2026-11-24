-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_zmodMulHom_apply
-- name    : GroundTheory.Arith.Abelian.zmodMulHom_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:41.211079+00:00
-- url     : https://prove2.me/theorems/e346e0ab-7455-4352-993a-14b705d7c9e6
-- title:
--   Abelian: zmod Mul Hom apply
-- statement:
--   The Abelian construction uses the zmod Mul Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L97-L102

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

theorem GroundTheory.Arith.Abelian.zmodMulHom_apply {m : ℕ} [NeZero m] (P : A) (hP : m • P = 0) (a : ZMod m) :
    zmodMulHom m P hP a = a.val • P := by sorry
