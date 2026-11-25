-- Prove2me | Theorems.Thm_GlobalTheory_idealCharacterL_continuation_ne_zero_one
-- name    : GlobalTheory.idealCharacterL_continuation_ne_zero_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:07.850916+00:00
-- url     : https://prove2.me/theorems/7702c0d6-edbe-4dc5-9164-d72f66c78896
-- title:
--   Global Theory: ideal Character L continuation ne zero one
-- statement:
--   The Global Theory construction uses the ideal Character L continuation ne zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdealCharacterLContinuationNeZeroOne.lean#L36-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdealCharacterLContinuationNeZeroOne.lean#L36-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_OneSubRePosOfNormLeHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DedekindZetaEulerProductMulSubOneEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
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

theorem GlobalTheory.idealCharacterL_continuation_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ)
    (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) →
    (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) →
    (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) →
    ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} →
    (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) →
    (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) →
    (∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → ∀ c : HeightOneSpectrum (𝓞 K) → ℂ,
    (∀ P, ‖c P‖ ≤ 1) → (∀ P, ¬ m ≤ P.asIdeal → c P = X P.asIdeal) →
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s | 0 < s.re} ∧ (∀ s : ℂ, 1 < s.re →
      L s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) ∧ L 1 ≠ 0 := by sorry
