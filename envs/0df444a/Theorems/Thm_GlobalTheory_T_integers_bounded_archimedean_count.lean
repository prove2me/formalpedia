-- Prove2me | Theorems.Thm_GlobalTheory_T_integers_bounded_archimedean_count
-- name    : GlobalTheory.T.integers_bounded_archimedean_count
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:33:55.641333+00:00
-- url     : https://prove2.me/theorems/f4204220-6574-427c-b8fd-336533af2146
-- title:
--   T: integers bounded archimedean count
-- statement:
--   The T construction uses the integers bounded archimedean count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegersBoundedArchimedeanCountStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegersBoundedArchimedeanCountStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegersBoundedArchimedeanCount
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegersBoundedArchimedeanCountStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integers_bounded_archimedean_count : ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
    {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
    ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N := by sorry
