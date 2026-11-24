-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_density_of_integrable_charFun
-- name    : GlobalTheory.CompanionTheory.SW.CharDensity.density_of_integrable_charFun
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:57.44358+00:00
-- url     : https://prove2.me/theorems/0d17f4f0-a02f-4a8a-86d3-190ab0bc6097
-- title:
--   Char Density: density of integrable char Fun
-- statement:
--   The Char Density construction uses the density of integrable char Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L270-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L270-L301

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

theorem GlobalTheory.CompanionTheory.SW.CharDensity.density_of_integrable_charFun :
    ∀ (κ : Type) [Fintype κ] (m : Measure (κ → ℝ)), IsFiniteMeasure m → Integrable (fun x : κ → ℝ => ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) → ∃ D : (κ → ℝ) → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = ∫ x : κ → ℝ, (∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, y w * x w : ℝ) : ℂ))) ∧ ∀ U : Set (κ → ℝ), MeasurableSet U → m U = ∫⁻ y in U, ENNReal.ofReal (D y) := by sorry
