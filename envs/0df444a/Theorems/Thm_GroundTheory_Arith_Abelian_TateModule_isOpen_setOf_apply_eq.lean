-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_TateModule_isOpen_setOf_apply_eq
-- name    : GroundTheory.Arith.Abelian.TateModule.isOpen_setOf_apply_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:42.141791+00:00
-- url     : https://prove2.me/theorems/142d0521-e972-4575-8eda-df8cfc2998c9
-- title:
--   Tate Module: is Open set Of apply eq
-- statement:
--   The Tate Module construction uses the is Open set Of apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L344-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L344-L349

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
variable {ℓ : ℕ} {A : Type*} [AddCommGroup A]

theorem GroundTheory.Arith.Abelian.TateModule.isOpen_setOf_apply_eq (k : ℕ) (a : A) :
    IsOpen {t : TateModule ℓ A | (t : ℕ → A) k = a} := by sorry
