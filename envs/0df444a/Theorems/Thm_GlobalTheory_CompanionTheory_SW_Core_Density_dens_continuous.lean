-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_dens_continuous
-- name    : GlobalTheory.CompanionTheory.SW.Core.Density.dens_continuous
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:38.233182+00:00
-- url     : https://prove2.me/theorems/8121fbe6-351e-4358-af4c-fd8b91e94d4e
-- title:
--   Density: dens continuous
-- statement:
--   The Density construction uses the dens continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L38-L48

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
variable [IsTopologicalAddGroup V]

theorem GlobalTheory.CompanionTheory.SW.Core.Density.dens_continuous [SecondCountableTopology V] [BorelSpace V] {χ : V → V → ℂ} {μ m : Measure V}
    (hc : Continuous (fun p : V × V => χ p.1 p.2)) (hn : ∀ x y, ‖χ x y‖ = 1)
    (hint : Integrable (mhat χ m) μ) : Continuous (dens χ μ m) := by sorry
