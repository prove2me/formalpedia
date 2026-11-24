-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LatticeCount_summable_of_lattice_decay
-- name    : GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:52:06.17492+00:00
-- url     : https://prove2.me/theorems/606db31a-06cb-4dd8-b0f6-c8b2ae92faa2
-- title:
--   Lattice Count: summable of lattice decay
-- statement:
--   The Lattice Count construction uses the summable of lattice decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOfLatticeDecay.lean#L38-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableOfLatticeDecay.lean#L38-L83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticeCount

theorem GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ)
    (hf : Function.Injective f) (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : ∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C)
    (hint : ∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) : Summable w := by sorry
