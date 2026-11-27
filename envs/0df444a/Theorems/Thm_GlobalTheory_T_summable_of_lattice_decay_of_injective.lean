-- Prove2me | Theorems.Thm_GlobalTheory_T_summable_of_lattice_decay_of_injective
-- name    : GlobalTheory.T.summable_of_lattice_decay_of_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:39:42.981052+00:00
-- url     : https://prove2.me/theorems/ea2946f7-2989-402b-94a0-5c5250a3313b
-- title:
--   T: summable of lattice decay of injective
-- statement:
--   The T construction uses the summable of lattice decay of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOfLatticeDecayStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOfLatticeDecayStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecay
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecayStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.summable_of_lattice_decay_of_injective : ∀ (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ), Function.Injective f → ∀ (N : ℕ), 0 < N → ∀ (C : ℝ), (∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C) → (∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) → Summable w := by sorry
