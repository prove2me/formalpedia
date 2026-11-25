-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_of_isRegularLocalRing
-- name    : GlobalTheory.isDomain_of_isRegularLocalRing
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:56.361842+00:00
-- url     : https://prove2.me/theorems/4959b485-f84e-4e77-b22f-731f73b82833
-- title:
--   Global Theory: is Domain of is Regular Local Ring
-- statement:
--   The Global Theory construction uses the is Domain of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L277-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L277-L280

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
variable {R : Type*} [CommRing R]
universe u in

theorem GlobalTheory.isDomain_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by sorry
