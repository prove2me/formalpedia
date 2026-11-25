-- Prove2me | Theorems.Thm_GlobalTheory_ringKrullDim_quotient_map_maximalIdeal_le_zero
-- name    : GlobalTheory.ringKrullDim_quotient_map_maximalIdeal_le_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:42.364822+00:00
-- url     : https://prove2.me/theorems/66020a05-9e1e-4d5b-a923-2c599c441634
-- title:
--   Global Theory: ring Krull Dim quotient map maximal Ideal le zero
-- statement:
--   The Global Theory construction uses the ring Krull Dim quotient map maximal Ideal le zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L526-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L526-L532

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
open ReciprocityTheory.CA
variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem GlobalTheory.ringKrullDim_quotient_map_maximalIdeal_le_zero [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B] :
    ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≤ 0 := by sorry
