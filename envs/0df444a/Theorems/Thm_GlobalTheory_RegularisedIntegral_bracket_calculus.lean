-- Prove2me | Theorems.Thm_GlobalTheory_RegularisedIntegral_bracket_calculus
-- name    : GlobalTheory.RegularisedIntegral.bracket_calculus
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:06.24432+00:00
-- url     : https://prove2.me/theorems/41224e99-e30a-4e6c-a4e0-9704a7c56d81
-- title:
--   Regularised Integral: bracket calculus
-- statement:
--   The Regularised Integral construction uses the bracket calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean#L406-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean#L406-L424

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

theorem GlobalTheory.RegularisedIntegral.bracket_calculus (H : SqIntegrable D α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {p : SS k r} (hp : D.inSS p) :
    (∀ x y, oneMinusDD (regBracket D F F' p) x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam (rr r) (Wd D) m x * gam (rr r) (Wd D) l y : ℝ) : ℂ) * QR D p m l F F' x y) ∧
    (∀ x, ContDiff ℝ 2 (fun y => regBracket D F F' p x y)) ∧
    (∀ y, ContDiff ℝ 2 (fun x => regBracket D F F' p x y -
      iteratedDeriv 2 (fun y' => regBracket D F F' p x y') y)) ∧
    (∀ x₁ x₂ : ℝ, (∫ t : ℝ × ℝ, oneMinusDD (regBracket D F F' p) t.1 t.2 *
        Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      (((1 + x₁ ^ 2) * (1 + x₂ ^ 2) : ℝ) : ℂ) *
        ∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 *
          Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) := by sorry
