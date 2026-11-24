-- Prove2me | Theorems.Thm_GlobalTheory_IdealSum_ideal_sum_periodic_dilate
-- name    : GlobalTheory.IdealSum.ideal_sum_periodic_dilate
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:04:41.818014+00:00
-- url     : https://prove2.me/theorems/dd56289a-1b3d-4e5a-b39f-afa9d569b438
-- title:
--   Ideal Sum: ideal sum periodic dilate
-- statement:
--   The Ideal Sum construction uses the ideal sum periodic dilate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdealSumPeriodicDilate.lean#L95-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdealSumPeriodicDilate.lean#L95-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptoticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealSumPeriodicDilate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.IdealSum

theorem GlobalTheory.IdealSum.ideal_sum_periodic_dilate : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (ψ : 𝓞 K → ℂ) (f : mixedSpace K → ℂ), m ≠ ⊥ → (∀ a b, a - b ∈ m → ψ a = ψ b) → ContDiff ℝ ∞ f → HasCompactSupport f → ∃ κ : ℂ, ∀ b : Ideal (𝓞 K), b ≠ ⊥ → b ⊔ m = ⊤ → ∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' α : b, ψ α * f (t • mixedEmbedding K ((α : 𝓞 K) : K)) - κ / (((Ideal.absNorm b : ℝ) * t ^ Module.finrank ℚ K : ℝ) : ℂ)‖ ≤ C * t ^ A := by sorry
