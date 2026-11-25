-- Prove2me | Theorems.Thm_GlobalTheory_RegularisedIntegral_coef_hasDerivAt
-- name    : GlobalTheory.RegularisedIntegral.coef_hasDerivAt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:21.058321+00:00
-- url     : https://prove2.me/theorems/0af2c0ea-39e8-47b8-8d1a-205dec261ffb
-- title:
--   Regularised Integral: coef has Deriv At
-- statement:
--   The Regularised Integral construction uses the coef has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean#L139-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean#L139-L256

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RegularisedIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {α : ℝ}

theorem GlobalTheory.RegularisedIntegral.coef_hasDerivAt (H : SqIntegrable D α) {A B A1 B1 : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : admitted α cA A) (hA1 : admitted α cA A1) (hB : admitted α cB B) (hB1 : admitted α cB B1)
    {p : SS k r} (hp : D.inSS p) {a b : ℝ → Mat k r} {κ : ℝ → ℝ} {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    {K : ℝ} (ha : ∀ t ∈ s, a t ∈ GV k r) (hb : ∀ t ∈ s, b t ∈ GV k r)
    (hKa : ∀ t ∈ s, gN (a t)⁻¹ ≤ K) (hKb : ∀ t ∈ s, gN (b t)⁻¹ ≤ K) (hκ : ∀ t ∈ s, |κ t| ≤ K)
    (dA : ∀ z ∈ GV k r, ∀ t ∈ s, HasDerivAt (fun t => A (a t * z * b t)) (κ t • A1 (a t * z * b t)) t)
    (dB : ∀ z ∈ GV k r, ∀ t ∈ s, HasDerivAt (fun t => B (a t * z * b t)) (κ t • B1 (a t * z * b t)) t) :
    HasDerivAt (fun t => Ph D (fun g => A (a t * g * b t)) (fun g => B (a t * g * b t)) p)
      ((κ t₀ : ℂ) * (Ph D (fun g => A1 (a t₀ * g * b t₀)) (fun g => B (a t₀ * g * b t₀)) p +
        Ph D (fun g => A (a t₀ * g * b t₀)) (fun g => B1 (a t₀ * g * b t₀)) p)) t₀ := by sorry
