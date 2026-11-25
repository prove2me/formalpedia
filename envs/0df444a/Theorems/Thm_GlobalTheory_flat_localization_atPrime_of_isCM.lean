-- Prove2me | Theorems.Thm_GlobalTheory_flat_localization_atPrime_of_isCM
-- name    : GlobalTheory.flat_localization_atPrime_of_isCM
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:05.675609+00:00
-- url     : https://prove2.me/theorems/5680679d-7928-47ef-bcb1-5daf54f549ed
-- title:
--   Global Theory: flat localization at Prime of is CM
-- statement:
--   The Global Theory construction uses the flat localization at Prime of is CM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L551-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L551-L563

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

theorem GlobalTheory.flat_localization_atPrime_of_isCM (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    [q.LiesOver p] [IsRegularLocalRing (Localization.AtPrime p)] [Algebra.QuasiFiniteAt A q]
    (hB : IsCM (Localization.AtPrime q)) (hd : p.height ≤ q.height) :
    Module.Flat A (Localization.AtPrime q) := by sorry
