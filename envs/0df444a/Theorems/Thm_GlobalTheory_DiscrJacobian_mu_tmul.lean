-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
-- name    : GlobalTheory.DiscrJacobian.mu_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:05.37112+00:00
-- url     : https://prove2.me/theorems/db2e2c82-a5ab-4cb8-8965-275ab4ac7c96
-- title:
--   Discr Jacobian: mu tmul
-- statement:
--   The Discr Jacobian construction uses the mu tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L22-L24

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

theorem GlobalTheory.DiscrJacobian.mu_tmul (s : S) (w : B) :
    _root_.GlobalTheory.DiscrJacobian.mu R S B (s ⊗ₜ w) = algebraMap S B s * w := by sorry
