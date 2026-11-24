-- Prove2me | Theorems.Thm_GlobalTheory_T_siegelReduced_integral_form_bounded_entries
-- name    : GlobalTheory.T.siegelReduced_integral_form_bounded_entries
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:41.845228+00:00
-- url     : https://prove2.me/theorems/e208d85e-564f-407a-a619-399ef00f43df
-- title:
--   T: siegel Reduced integral form bounded entries
-- statement:
--   The T construction uses the siegel Reduced integral form bounded entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntriesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntriesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntriesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.siegelReduced_integral_form_bounded_entries : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) → B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) → (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X → ∀ i j, |(B i j : ℝ)| ≤ C' := by sorry
