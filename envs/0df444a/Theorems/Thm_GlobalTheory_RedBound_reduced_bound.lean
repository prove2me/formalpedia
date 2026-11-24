-- Prove2me | Theorems.Thm_GlobalTheory_RedBound_reduced_bound
-- name    : GlobalTheory.RedBound.reduced_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:07.665344+00:00
-- url     : https://prove2.me/theorems/9c822ef5-bcc3-4777-b92d-2ef2c1d33641
-- title:
--   Red Bound: reduced bound
-- statement:
--   The Red Bound construction uses the reduced bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntries.lean#L53-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntries.lean#L53-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.RedBound

theorem GlobalTheory.RedBound.reduced_bound : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) →
    B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) →
    (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X →
    ∀ i j, |(B i j : ℝ)| ≤ C' := by sorry
