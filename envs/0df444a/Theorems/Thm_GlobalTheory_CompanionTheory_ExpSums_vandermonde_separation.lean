-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExpSums_vandermonde_separation
-- name    : GlobalTheory.CompanionTheory.ExpSums.vandermonde_separation
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:08.21868+00:00
-- url     : https://prove2.me/theorems/1fac1c4f-e332-440c-88a3-b4d7166d30f5
-- title:
--   Exp Sums: vandermonde separation
-- statement:
--   The Exp Sums construction uses the vandermonde separation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VandermondeSeparation.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VandermondeSeparation.lean#L7-L36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VandermondeSeparation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExpSums
open Matrix

theorem GlobalTheory.CompanionTheory.ExpSums.vandermonde_separation (r : ℕ) (α : Fin r → ℂ) (hα : Function.Injective α) :
    ∃ C : ℝ, ∀ (c : Fin r → ℂ) (i : Fin r),
      ‖c i‖ ≤ C * ∑ s : Fin r, ‖∑ k, c k * α k ^ (s : ℕ)‖ := by sorry
