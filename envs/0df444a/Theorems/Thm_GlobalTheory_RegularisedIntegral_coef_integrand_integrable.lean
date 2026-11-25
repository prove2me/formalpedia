-- Prove2me | Theorems.Thm_GlobalTheory_RegularisedIntegral_coef_integrand_integrable
-- name    : GlobalTheory.RegularisedIntegral.coef_integrand_integrable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:50:04.093058+00:00
-- url     : https://prove2.me/theorems/3460a00c-f709-5067-921f-a17bbcd5415f
-- title:
--   Regularised Integral: coef integrand integrable
-- statement:
--   The Regularised Integral construction uses the coef integrand integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean#L83-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean#L83-L89

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

theorem GlobalTheory.RegularisedIntegral.coef_integrand_integrable (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : admitted α cA A) (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) :
    Integrable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by sorry
