-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_smoothed_eq
-- name    : GlobalTheory.CompanionTheory.SW.CharDensity.smoothed_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:08.615856+00:00
-- url     : https://prove2.me/theorems/ba23c852-20ca-4184-941a-a523a4f6c18d
-- title:
--   Char Density: smoothed eq
-- statement:
--   The Char Density construction uses the smoothed eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L89-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L89-L119

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.CompanionTheory.SW.CharDensity.smoothed_eq (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) (y : V) :
    ∫ x, phi μ x * (Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))) =
      ((∫ z, ker b (z - y) ∂μ : ℝ) : ℂ) := by sorry
