-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_isRegularRing_of_isRegularRing
-- name    : GlobalTheory.flat_of_isRegularRing_of_isRegularRing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:13.451107+00:00
-- url     : https://prove2.me/theorems/d09ab660-a102-416f-ae17-3312882f7091
-- title:
--   Global Theory: flat of is Regular Ring of is Regular Ring
-- statement:
--   The Global Theory construction uses the flat of is Regular Ring of is Regular Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L572-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L572-L575

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

theorem GlobalTheory.flat_of_isRegularRing_of_isRegularRing [IsRegularRing A] [IsRegularRing B]
    [Algebra.QuasiFinite A B]
    (hd : ∀ q : Ideal B, q.IsMaximal → (q.under A).height ≤ q.height) : Module.Flat A B := by sorry
