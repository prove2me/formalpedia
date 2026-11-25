-- Prove2me | Theorems.Thm_GlobalTheory_isRegular_of_length_eq_spanFinrank
-- name    : GlobalTheory.isRegular_of_length_eq_spanFinrank
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:19.34539+00:00
-- url     : https://prove2.me/theorems/83799271-7155-4afa-8270-14996e851a80
-- title:
--   Global Theory: is Regular of length eq span Finrank
-- statement:
--   The Global Theory construction uses the is Regular of length eq span Finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L331-L334

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
universe u

theorem GlobalTheory.isRegular_of_length_eq_spanFinrank [IsRegularLocalRing R] {xs : List R}
    (h : Ideal.ofList xs = maximalIdeal R) (hd : xs.length = (maximalIdeal R).spanFinrank) :
    RingTheory.Sequence.IsRegular R xs := by sorry
