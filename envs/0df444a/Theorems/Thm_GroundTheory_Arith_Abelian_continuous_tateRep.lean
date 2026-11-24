-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_continuous_tateRep
-- name    : GroundTheory.Arith.Abelian.continuous_tateRep
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:26:11.778794+00:00
-- url     : https://prove2.me/theorems/840ef62b-7a3b-46f2-a360-1d70c29571cf
-- title:
--   Abelian: continuous tate Rep
-- statement:
--   The Abelian construction uses the continuous tate Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L385-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L385-L412

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

theorem GroundTheory.Arith.Abelian.continuous_tateRep {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* AddMonoid.End A) (hφ : ∀ a : A, IsOpen {g : G | φ g a = a}) :
    Continuous (fun p : G × TateModule ℓ A => tateRep φ p.1 p.2) := by sorry
