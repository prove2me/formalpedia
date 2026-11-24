-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OpenSubgroupTransversal_main
-- name    : GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:25.191624+00:00
-- url     : https://prove2.me/theorems/6aaf2b35-7773-4409-ae27-ffe706773670
-- title:
--   Open Subgroup Transversal: main
-- statement:
--   The Open Subgroup Transversal construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCosetRepresentatives.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCosetRepresentatives.lean#L35-L38

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCosetRepresentatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OpenSubgroupTransversal

theorem GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A →
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by sorry
