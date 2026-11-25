-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_quotSMulTop
-- name    : GlobalTheory.IsQuasiRegularSeq.quotSMulTop
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:03.888191+00:00
-- url     : https://prove2.me/theorems/304cf6c0-2076-409c-b80c-5d61291fdc22
-- title:
--   Is Quasi Regular Seq: quot SMul Top
-- statement:
--   The Is Quasi Regular Seq construction uses the quot SMul Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L201-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L201-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]

theorem GlobalTheory.IsQuasiRegularSeq.quotSMulTop {f : Option ι → R} (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (QuotSMulTop (f none) M) (f ∘ some) := by sorry
