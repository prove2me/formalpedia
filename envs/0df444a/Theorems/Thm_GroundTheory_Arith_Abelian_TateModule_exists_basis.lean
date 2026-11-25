-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_TateModule_exists_basis
-- name    : GroundTheory.Arith.Abelian.TateModule.exists_basis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:27:32.086664+00:00
-- url     : https://prove2.me/theorems/9ee6ef72-06e7-4335-a8a6-f04aa3767abb
-- title:
--   Tate Module: exists basis
-- statement:
--   The Tate Module construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L215-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L215-L289

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

theorem GroundTheory.Arith.Abelian.TateModule.exists_basis
    (hcard : ∀ k, Nat.card {P : A // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2)
    (hbase : ∃ P Q : A, ℓ • P = 0 ∧ ℓ • Q = 0 ∧ ∀ a b : ℕ, a • P + b • Q = 0 → ℓ ∣ a ∧ ℓ ∣ b) :
    Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ A)) := by sorry
