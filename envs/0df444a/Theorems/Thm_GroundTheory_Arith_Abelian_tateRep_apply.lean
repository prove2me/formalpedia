-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_tateRep_apply
-- name    : GroundTheory.Arith.Abelian.tateRep_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:57:01.472983+00:00
-- url     : https://prove2.me/theorems/11539357-53d0-40de-9af2-ad96b0d16f50
-- title:
--   Abelian: tate Rep apply
-- statement:
--   The Abelian construction uses the tate Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L380-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L380-L383

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

theorem GroundTheory.Arith.Abelian.tateRep_apply {G : Type*} [Monoid G] (φ : G →* AddMonoid.End A) (g : G)
    (t : TateModule ℓ A) (k : ℕ) :
    ((tateRep φ g t : TateModule ℓ A) : ℕ → A) k = φ g ((t : ℕ → A) k) := by sorry
