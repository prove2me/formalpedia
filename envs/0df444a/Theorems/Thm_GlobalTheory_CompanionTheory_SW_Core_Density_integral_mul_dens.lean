-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_integral_mul_dens
-- name    : GlobalTheory.CompanionTheory.SW.Core.Density.integral_mul_dens
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:40.665469+00:00
-- url     : https://prove2.me/theorems/c95cd5df-c90d-489e-bbd0-bffd441e5596
-- title:
--   Density: integral mul dens
-- statement:
--   The Density construction uses the integral mul dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L80-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L80-L125

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
variable [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [BorelSpace V]

theorem GlobalTheory.CompanionTheory.SW.Core.Density.integral_mul_dens {χ : V → V → ℂ} {μ m : Measure V} [μ.IsAddHaarMeasure] [IsFiniteMeasure m]
    (h : NADual V χ μ) (hc : Continuous (fun p : V × V => χ p.1 p.2)) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (hint : Integrable (mhat χ m) μ) {φ : V → ℂ} (hφ : SB φ) :
    ∫ x, φ x * dens χ μ m x ∂μ = ∫ z, φ z ∂m := by sorry
