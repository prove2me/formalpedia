-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_quotSMulTop_tail
-- name    : GlobalTheory.IsQuasiRegularSeq.quotSMulTop_tail
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:42.89329+00:00
-- url     : https://prove2.me/theorems/20fbaf52-2c8e-4399-b107-fa461ced4b30
-- title:
--   Is Quasi Regular Seq: quot SMul Top tail
-- statement:
--   The Is Quasi Regular Seq construction uses the quot SMul Top tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L307-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L307-L310

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
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem GlobalTheory.IsQuasiRegularSeq.quotSMulTop_tail {n : ℕ} {f : Fin (n + 1) → R}
    (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (QuotSMulTop (f 0) M) fun i : Fin n => f i.succ := by sorry
