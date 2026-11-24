-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_OrthMeas_chiB_mulVec_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.Core.OrthMeas.chiB_mulVec_mulVec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:04:26.168836+00:00
-- url     : https://prove2.me/theorems/d3332ed5-21a1-45a3-9c04-8fb48631349b
-- title:
--   Orth Meas: chi B mul Vec mul Vec
-- statement:
--   The Orth Meas construction uses the chi B mul Vec mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WeilOrthogonalGroupInvariance.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WeilOrthogonalGroupInvariance.lean#L9-L16

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

theorem GlobalTheory.CompanionTheory.SW.Core.OrthMeas.chiB_mulVec_mulVec {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    (ψ : AddChar R ℂ) (B g : Matrix ι ι R) (hg : gᵀ * B * g = B) (x y : ι → R) :
    chiB ψ B (g *ᵥ x) (g *ᵥ y) = chiB ψ B x y := by sorry
