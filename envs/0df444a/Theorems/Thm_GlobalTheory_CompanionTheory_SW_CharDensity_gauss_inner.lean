-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_gauss_inner
-- name    : GlobalTheory.CompanionTheory.SW.CharDensity.gauss_inner
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:13.790679+00:00
-- url     : https://prove2.me/theorems/91330893-8593-474f-96a2-84bfddcd00b3
-- title:
--   Char Density: gauss inner
-- statement:
--   The Char Density construction uses the gauss inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L73-L87

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

theorem GlobalTheory.CompanionTheory.SW.CharDensity.gauss_inner {b : ℝ} (hb : 0 < b) (u : V) :
    ∫ x : V, Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ u x : ℝ) : ℂ)) = (ker b u : ℂ) := by sorry
