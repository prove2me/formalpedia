-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_of_isRegular
-- name    : GlobalTheory.isQuasiRegularSeq_of_isRegular
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:14.819304+00:00
-- url     : https://prove2.me/theorems/ffe6c6a6-8e26-5782-bb1f-0c2ff8e98773
-- title:
--   Global Theory: is Quasi Regular Seq of is Regular
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq of is Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L303-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L303-L305

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

theorem GlobalTheory.isQuasiRegularSeq_of_isRegular {n : ℕ} {f : Fin n → R}
    (h : RingTheory.Sequence.IsRegular M (List.ofFn f)) : IsQuasiRegularSeq M f := by sorry
