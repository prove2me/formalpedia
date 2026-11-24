-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_der_mul
-- name    : GlobalTheory.DiscrJacobian.der_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:49:05.229001+00:00
-- url     : https://prove2.me/theorems/620f4903-a9d4-4be0-a123-494b622e0982
-- title:
--   Discr Jacobian: der mul
-- statement:
--   The Discr Jacobian construction uses the der mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L132-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L132-L147

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
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]
open scoped TensorProduct
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]

theorem GlobalTheory.DiscrJacobian.der_mul (D : Derivation R S S) (y z : S ⊗[R] B) :
    _root_.GlobalTheory.DiscrJacobian.der D (y * z) =
      _root_.GlobalTheory.DiscrJacobian.mu R S B y * _root_.GlobalTheory.DiscrJacobian.der D z +
        _root_.GlobalTheory.DiscrJacobian.mu R S B z * _root_.GlobalTheory.DiscrJacobian.der D y := by sorry
