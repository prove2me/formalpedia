-- Prove2me | Theorems.Thm_GlobalTheory_smoothedSum_main_term_representatives
-- name    : GlobalTheory.smoothedSum_main_term_representatives
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:42.746296+00:00
-- url     : https://prove2.me/theorems/170ed5f3-e756-4665-9e04-6870d1b8b23a
-- title:
--   Global Theory: smoothed Sum main term representatives
-- statement:
--   The Global Theory construction uses the smoothed Sum main term representatives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SmoothedIdealCharacterSumMainTermIdealClassRepre.lean#L341-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SmoothedIdealCharacterSumMainTermIdealClassRepre.lean#L341-L448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealSumPeriodicDilate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SmoothedIdealCharacterSumMainTermIdealClassRepre
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
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem GlobalTheory.smoothedSum_main_term_representatives : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) → (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) → (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} → (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) → ∀ (wt : ℝ → ℂ), ContDiff ℝ ∞ wt → (∃ a b : ℝ, 0 < a ∧ ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) → ∃ κ : ℂ, ∀ b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰, Function.Bijective (fun c => ClassGroup.mk0 (b c)) → (∀ c, (b c : Ideal (𝓞 K)) ⊔ m = ⊤) → ∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' I, X I * wt (t * (Ideal.absNorm I : ℝ)) - (κ * ∑ c, (X (b c))⁻¹) / (t : ℂ)‖ ≤ C * t ^ A := by sorry
