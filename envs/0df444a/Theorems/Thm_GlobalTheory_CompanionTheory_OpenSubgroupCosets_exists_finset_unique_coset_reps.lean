-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OpenSubgroupCosets_exists_finset_unique_coset_reps
-- name    : GlobalTheory.CompanionTheory.OpenSubgroupCosets.exists_finset_unique_coset_reps
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:17.232351+00:00
-- url     : https://prove2.me/theorems/20c34963-69bb-449b-8a12-919140618b9e
-- title:
--   Open Subgroup Cosets: exists finset unique coset reps
-- statement:
--   The Open Subgroup Cosets construction uses the exists finset unique coset reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompactSetFiniteCosetRepresentatives.lean#L6-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompactSetFiniteCosetRepresentatives.lean#L6-L42

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompactSetFiniteCosetRepresentatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OpenSubgroupCosets

theorem GlobalTheory.CompanionTheory.OpenSubgroupCosets.exists_finset_unique_coset_reps :
    ∀ {E : Type} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
      (D : AddSubgroup E), IsOpen (D : Set E) → ∀ (R : Set E), IsCompact R →
      ∃ S : Finset E, (∀ s ∈ S, s ∈ R) ∧ ∀ x ∈ R, ∃! s, s ∈ S ∧ x - s ∈ D := by sorry
