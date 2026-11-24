-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_finiteDimensional_of_compact_coercive
-- name    : GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:27.747374+00:00
-- url     : https://prove2.me/theorems/f50ae78f-cc69-448e-b36b-8d873eb89cf7
-- title:
--   Glob: finite Dimensional of compact coercive
-- statement:
--   The Glob construction uses the finite Dimensional of compact coercive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteDimensionalOfCompactCoercive.lean#L7-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteDimensionalOfCompactCoercive.lean#L7-L48

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteDimensionalOfCompactCoercive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob

theorem GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c →
        (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by sorry
