-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_TateModule_map_apply
-- name    : GroundTheory.Arith.Abelian.TateModule.map_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:39.114412+00:00
-- url     : https://prove2.me/theorems/c6d45e1e-b00c-56c8-b372-75c5e39053fd
-- title:
--   Tate Module: map apply
-- statement:
--   The Tate Module construction uses the map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L364-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L364-L366

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

theorem GroundTheory.Arith.Abelian.TateModule.map_apply (f : A →+ A) (t : TateModule ℓ A) (k : ℕ) :
    ((TateModule.map f t : TateModule ℓ A) : ℕ → A) k = f ((t : ℕ → A) k) := by sorry
