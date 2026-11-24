-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_nonempty_addEquiv_zmod_prod
-- name    : GroundTheory.Arith.Abelian.nonempty_addEquiv_zmod_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:43.051182+00:00
-- url     : https://prove2.me/theorems/5cc0a263-2407-400c-a7d0-fa11c2b05b8d
-- title:
--   Abelian: nonempty add Equiv zmod prod
-- statement:
--   The Abelian construction uses the nonempty add Equiv zmod prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean#L42-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean#L42-L150

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

theorem GroundTheory.Arith.Abelian.nonempty_addEquiv_zmod_prod {n : ℕ} (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (hcard : Nat.card A = n ^ 2)
    (hker : ∀ m, m ∣ n → Nat.card {a : A // m • a = 0} ≤ m ^ 2) :
    Nonempty (A ≃+ ZMod n × ZMod n) := by sorry
