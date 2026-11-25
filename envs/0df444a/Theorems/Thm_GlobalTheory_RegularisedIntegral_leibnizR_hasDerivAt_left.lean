-- Prove2me | Theorems.Thm_GlobalTheory_RegularisedIntegral_leibnizR_hasDerivAt_left
-- name    : GlobalTheory.RegularisedIntegral.leibnizR_hasDerivAt_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:13:18.862452+00:00
-- url     : https://prove2.me/theorems/9bffb32b-b950-4bdd-b47c-9282d9635025
-- title:
--   Regularised Integral: leibniz R has Deriv At left
-- statement:
--   The Regularised Integral construction uses the leibniz R has Deriv At left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean#L368-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean#L368-L379

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

theorem GlobalTheory.RegularisedIntegral.leibnizR_hasDerivAt_left (H : SqIntegrable D α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l (m + 1) A) (hB : AdmW α cB l (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QR D p m l A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QR D p (m + 1) l A B x y) x := by sorry
