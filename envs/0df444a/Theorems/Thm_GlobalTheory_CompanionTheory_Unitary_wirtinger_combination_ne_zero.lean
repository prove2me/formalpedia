-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Unitary_wirtinger_combination_ne_zero
-- name    : GlobalTheory.CompanionTheory.Unitary.wirtinger_combination_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:36.207945+00:00
-- url     : https://prove2.me/theorems/2abbcae0-ee2b-4fb5-8499-54cf6322781e
-- title:
--   Unitary: wirtinger combination ne zero
-- statement:
--   The Unitary construction uses the wirtinger combination ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WirtingerCombinationNeZero.lean#L5-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WirtingerCombinationNeZero.lean#L5-L98

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WirtingerCombinationNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Unitary

theorem GlobalTheory.CompanionTheory.Unitary.wirtinger_combination_ne_zero : ∀ (χ : ℂ → ℂ), Continuous χ → (∀ z w, χ (z + w) = χ z * χ w) →
    (∀ z, ‖χ z‖ = 1) → (∃ z, χ z ≠ 1) → ∀ (D : ℂ → ℂ),
    (∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) →
    ∀ β : ℂ, β ≠ 0 → D β - Complex.I * D (β * Complex.I) ≠ 0 := by sorry
