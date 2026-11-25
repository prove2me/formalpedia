-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_exists_socle
-- name    : GlobalTheory.DiscrJacobian.exists_socle
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:57.966797+00:00
-- url     : https://prove2.me/theorems/af5db82a-a4c6-53f0-8285-50ba05aa9c51
-- title:
--   Discr Jacobian: exists socle
-- statement:
--   The Discr Jacobian construction uses the exists socle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L164-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L164-L174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

theorem GlobalTheory.DiscrJacobian.exists_socle {V : Type} [AddCommGroup V] [Module R V] (n : Ideal B) (φ : B →ₗ[R] V)
    (hφ : φ ≠ 0) (N : ℕ) (hN : ∀ w ∈ n ^ N, φ w = 0) :
    ∃ y, φ y ≠ 0 ∧ ∀ w ∈ n, φ (w * y) = 0 := by sorry
