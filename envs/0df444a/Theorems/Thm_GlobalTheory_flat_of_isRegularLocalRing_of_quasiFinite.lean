-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_isRegularLocalRing_of_quasiFinite
-- name    : GlobalTheory.flat_of_isRegularLocalRing_of_quasiFinite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:22.852826+00:00
-- url     : https://prove2.me/theorems/4321968c-a07b-4c44-82cf-4002afe9d5bd
-- title:
--   Global Theory: flat of is Regular Local Ring of quasi Finite
-- statement:
--   The Global Theory construction uses the flat of is Regular Local Ring of quasi Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L540-L543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L540-L543

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

theorem GlobalTheory.flat_of_isRegularLocalRing_of_quasiFinite [IsRegularLocalRing A] [IsRegularLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B]
    (hd : ringKrullDim A = ringKrullDim B) : Module.Flat A B := by sorry
