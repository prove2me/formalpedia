-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Bump_exists_nonneg_bump
-- name    : GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:15.003578+00:00
-- url     : https://prove2.me/theorems/827e4225-0b08-539e-a372-55c7e45093e2
-- title:
--   Bump: exists nonneg bump
-- statement:
--   The Bump construction uses the exists nonneg bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsNonnegBump.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsNonnegBump.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsNonnegBump
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bump

theorem GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump :
    ∀ {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] (x : X) (N : Set X),
      N ∈ 𝓝 x → ∃ φ : X → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ 0 ≤ φ ∧ φ x ≠ 0 ∧
        Function.support φ ⊆ N := by sorry
