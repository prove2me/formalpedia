-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_exists_addOrderOf_eq_of_card
-- name    : GroundTheory.Arith.Abelian.exists_addOrderOf_eq_of_card
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:44.867111+00:00
-- url     : https://prove2.me/theorems/452682c8-2901-4fc1-b5c6-774d5dbbeaf7
-- title:
--   Abelian: exists add Order Of eq of card
-- statement:
--   The Abelian construction uses the exists add Order Of eq of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean#L12-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean#L12-L30

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
variable {A : Type*} [AddCommGroup A]

theorem GroundTheory.Arith.Abelian.exists_addOrderOf_eq_of_card {n : ℕ} (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (hcard : Nat.card A = n ^ 2)
    (hker : ∀ m, m ∣ n → Nat.card {a : A // m • a = 0} ≤ m ^ 2) :
    ∃ P : A, addOrderOf P = n := by sorry
