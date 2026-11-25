-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_isSMulRegular_of_iInf_eq_bot
-- name    : GlobalTheory.IsQuasiRegularSeq.isSMulRegular_of_iInf_eq_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:42.798954+00:00
-- url     : https://prove2.me/theorems/8429d303-fed4-4390-aec5-9868ceebdffb
-- title:
--   Is Quasi Regular Seq: is SMul Regular of i Inf eq bot
-- statement:
--   The Is Quasi Regular Seq construction uses the is SMul Regular of i Inf eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L194-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L194-L199

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

theorem GlobalTheory.IsQuasiRegularSeq.isSMulRegular_of_iInf_eq_bot {f : ι → R} (h : IsQuasiRegularSeq M f)
    (hsep : (⨅ a : ℕ, Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) = ⊥) (i : ι) :
    IsSMulRegular M (f i) := by sorry
