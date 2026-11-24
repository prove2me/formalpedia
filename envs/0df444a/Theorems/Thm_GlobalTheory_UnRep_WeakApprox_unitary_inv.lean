-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_WeakApprox_unitary_inv
-- name    : GlobalTheory.UnRep.WeakApprox.unitary_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:29.522299+00:00
-- url     : https://prove2.me/theorems/068e795a-da33-4d67-9c52-195d85f114bc
-- title:
--   Weak Approx: unitary inv
-- statement:
--   The Weak Approx construction uses the unitary inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L244-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L244-L250

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

theorem GlobalTheory.UnRep.WeakApprox.unitary_inv {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G g h : Matrix (Fin n) (Fin n) R)
    (hgh : g * h = 1) (hg : gᵀ * G * g.map σ = G) : hᵀ * G * h.map σ = G := by sorry
