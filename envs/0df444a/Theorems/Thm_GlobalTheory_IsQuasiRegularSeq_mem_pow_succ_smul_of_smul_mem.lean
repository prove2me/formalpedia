-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_mem_pow_succ_smul_of_smul_mem
-- name    : GlobalTheory.IsQuasiRegularSeq.mem_pow_succ_smul_of_smul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:51.168577+00:00
-- url     : https://prove2.me/theorems/eecf73a4-19a4-497e-89e6-006e2ed29d78
-- title:
--   Is Quasi Regular Seq: mem pow succ smul of smul mem
-- statement:
--   The Is Quasi Regular Seq construction uses the mem pow succ smul of smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L168-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing.lean#L168-L183

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

theorem GlobalTheory.IsQuasiRegularSeq.mem_pow_succ_smul_of_smul_mem {f : ι → R} (h : IsQuasiRegularSeq M f)
    (i : ι) {a : ℕ} {m : M} (hm : m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M))
    (hfm : f i • m ∈ (Ideal.span (Set.range f) ^ (a + 2) • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) := by sorry
