-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
-- name    : GlobalTheory.DiscrJacobian.der_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:05.90641+00:00
-- url     : https://prove2.me/theorems/dab4b47e-08d0-4445-af01-39c9697b5608
-- title:
--   Discr Jacobian: der tmul
-- statement:
--   The Discr Jacobian construction uses the der tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L125-L127

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

theorem GlobalTheory.DiscrJacobian.der_tmul (D : Derivation R S S) (s : S) (w : B) :
    _root_.GlobalTheory.DiscrJacobian.der D (s ⊗ₜ[R] w) = algebraMap S B (D s) * w := by sorry
