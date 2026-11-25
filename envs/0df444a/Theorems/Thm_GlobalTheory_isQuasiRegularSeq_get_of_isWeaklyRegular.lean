-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_get_of_isWeaklyRegular
-- name    : GlobalTheory.isQuasiRegularSeq_get_of_isWeaklyRegular
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:18.69804+00:00
-- url     : https://prove2.me/theorems/50e9f397-394c-4802-9dd9-66e00b56c70d
-- title:
--   Global Theory: is Quasi Regular Seq get of is Weakly Regular
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq get of is Weakly Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L299-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L299-L301

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

theorem GlobalTheory.isQuasiRegularSeq_get_of_isWeaklyRegular {rs : List R} (h : IsWeaklyRegular M rs) :
    IsQuasiRegularSeq M rs.get := by sorry
