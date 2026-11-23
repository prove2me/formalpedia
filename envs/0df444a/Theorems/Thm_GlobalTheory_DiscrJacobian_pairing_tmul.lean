-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
-- name    : GlobalTheory.DiscrJacobian.pairing_tmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:10.630474+00:00
-- url     : https://prove2.me/theorems/6a94dc94-6110-46f8-af9b-e4def6c82b4f
-- title:
--   Discr Jacobian: pairing tmul
-- statement:
--   The Discr Jacobian construction uses the pairing tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L160-L162

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
open scoped TensorProduct
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

theorem GlobalTheory.DiscrJacobian.pairing_tmul (ρ : B →ₐ[R] C) (ψ : B →ₗ[R] C) (u w : B) :
    _root_.GlobalTheory.DiscrJacobian.pairing ρ ψ (u ⊗ₜ w) = ρ u * ψ w := by sorry
