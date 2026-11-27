-- Prove2me | Theorems.Thm_GlobalTheory_free_of_isRegularLocalRing_of_finite
-- name    : GlobalTheory.free_of_isRegularLocalRing_of_finite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:16.044793+00:00
-- url     : https://prove2.me/theorems/205012db-1ee3-457d-9496-a66bc32184ae
-- title:
--   Global Theory: free of is Regular Local Ring of finite
-- statement:
--   The Global Theory construction uses the free of is Regular Local Ring of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L545-L549
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L545-L549

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

theorem GlobalTheory.free_of_isRegularLocalRing_of_finite [IsRegularLocalRing A] [IsRegularLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    (hd : ringKrullDim A = ringKrullDim B) : Module.Free A B := by sorry
