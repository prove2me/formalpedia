-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_OrthMeas_orth_meas
-- name    : GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:03:45.361012+00:00
-- url     : https://prove2.me/theorems/16b87b7e-31a4-48ed-a6c5-161d7284156d
-- title:
--   Orth Meas: orth meas
-- statement:
--   The Orth Meas construction uses the orth meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WeilOrthogonalGroupInvariance.lean#L83-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WeilOrthogonalGroupInvariance.lean#L83-L111

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WeilOrthogonalGroupInvariance
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.OrthMeas

theorem GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)),
    NAQuad ψ h B μ → ∀ g : Matrix ι ι R, IsUnit g.det → gᵀ * B * g = B →
      Measure.map (fun x => g *ᵥ x) μ = μ ∧ ∀ φ : (ι → R) → ℂ, SB φ →
        SB (fun x => φ (g *ᵥ x)) ∧
          ∀ y, fou (chiB ψ B) μ (fun x => φ (g *ᵥ x)) y = fou (chiB ψ B) μ φ (g *ᵥ y) := by sorry
