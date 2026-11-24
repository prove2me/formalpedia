-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_WeakApprox_preserves_form_smul_idempotent_glue
-- name    : GlobalTheory.UnRep.WeakApprox.preserves_form_smul_idempotent_glue
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:23:25.591022+00:00
-- url     : https://prove2.me/theorems/c03f8eca-2c05-4001-8406-d47f0e602add
-- title:
--   Weak Approx: preserves form smul idempotent glue
-- statement:
--   The Weak Approx construction uses the preserves form smul idempotent glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L77-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.WeakApprox

theorem GlobalTheory.UnRep.WeakApprox.preserves_form_smul_idempotent_glue {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G h : Matrix (Fin n) (Fin n) R)
    (e l : R) (he : e * e = e) (hσ : σ e = e) (hl : l * σ l = 1) (hh : hᵀ * G * h.map σ = G) :
    (l • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)))ᵀ * G *
      (l • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R))).map σ = G := by sorry
