-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_WeakApprox_idem_diff
-- name    : GlobalTheory.UnRep.WeakApprox.idem_diff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:23:20.916729+00:00
-- url     : https://prove2.me/theorems/38d6d5a1-f5d7-45cc-b1c2-9c08b6babc3c
-- title:
--   Weak Approx: idem diff
-- statement:
--   The Weak Approx construction uses the idem diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L61-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L61-L75

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

theorem GlobalTheory.UnRep.WeakApprox.idem_diff {R M : Type} [CommRing R] [Ring M] [Algebra R M] (e : R) (he : e * e = e)
    (S T U V W : M) (hU : U * (1 + S) = 1) (hU' : (1 + S) * U = 1) (hV : V * (1 + T) = 1)
    (hV' : (1 + T) * V = 1) (hW : W * (1 + e • (-((S - T) * U))) = 1) :
    e • (V - U) = e • (U * W * (S - T) * U) := by sorry
