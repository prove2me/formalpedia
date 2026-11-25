-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_isWeaklyRegular
-- name    : GlobalTheory.IsQuasiRegularSeq.isWeaklyRegular
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:12.707805+00:00
-- url     : https://prove2.me/theorems/c19928d2-51b6-4d2b-9117-865240edf13d
-- title:
--   Is Quasi Regular Seq: is Weakly Regular
-- statement:
--   The Is Quasi Regular Seq construction uses the is Weakly Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L312-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L312-L323

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

theorem GlobalTheory.IsQuasiRegularSeq.isWeaklyRegular [IsNoetherianRing R] [Module.Finite R M] {n : ℕ}
    {f : Fin n → R} (h : IsQuasiRegularSeq M f) (hf : ∀ i, f i ∈ (⊥ : Ideal R).jacobson) :
    IsWeaklyRegular M (List.ofFn f) := by sorry
