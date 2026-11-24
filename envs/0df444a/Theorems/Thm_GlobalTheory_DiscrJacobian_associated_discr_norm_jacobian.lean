-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_associated_discr_norm_jacobian
-- name    : GlobalTheory.DiscrJacobian.associated_discr_norm_jacobian
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:54.946267+00:00
-- url     : https://prove2.me/theorems/68ec7ce0-ab5c-4ef8-b905-ca371fe93380
-- title:
--   Discr Jacobian: associated discr norm jacobian
-- statement:
--   The Discr Jacobian construction uses the associated discr norm jacobian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L384-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L384-L586

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
open MvPowerSeries IsLocalRing
open MvPowerSeries IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 800000

theorem GlobalTheory.DiscrJacobian.associated_discr_norm_jacobian (R : Type) [CommRing R] [IsLocalRing R]
    (g d : ℕ) (f : Fin g → MvPowerSeries (Fin g) R)
    (b : Module.Basis (Fin d) R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))
    (hf : ∀ i, constantCoeff (f i) ∈ maximalIdeal R) :
    Associated (Algebra.discr R b) (Algebra.norm R (Ideal.Quotient.mk (Ideal.span (Set.range f))
      (Matrix.of fun i j => pderiv R j (f i)).det)) := by sorry
