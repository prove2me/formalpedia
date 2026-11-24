-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_exists_density
-- name    : GlobalTheory.CompanionTheory.SW.Core.Density.exists_density
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:41.823806+00:00
-- url     : https://prove2.me/theorems/35fb1d4a-dd99-45dc-a554-56401b16d6dc
-- title:
--   Density: exists density
-- statement:
--   The Density construction uses the exists density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L252-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L252-L300

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]

theorem GlobalTheory.CompanionTheory.SW.Core.Density.exists_density : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ (m : Measure V), IsFiniteMeasure m →
    Integrable (fun y => ∫ x, χ x y ∂m) μ → ∃ D : V → ℝ, Continuous D ∧ (∀ x, 0 ≤ D x) ∧
    (∀ x, (D x : ℂ) = ∫ y, (∫ z, χ z y ∂m) * χ (-x) y ∂μ) ∧
    ∀ U : Set V, MeasurableSet U → m U = ∫⁻ x in U, ENNReal.ofReal (D x) ∂μ := by sorry
