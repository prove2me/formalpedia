-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_OrthMeas_perp_image
-- name    : GlobalTheory.CompanionTheory.SW.Core.OrthMeas.perp_image
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:03:57.8818+00:00
-- url     : https://prove2.me/theorems/b1bbe9f1-6e1b-4d56-9355-c5be8771f0a1
-- title:
--   Orth Meas: perp image
-- statement:
--   The Orth Meas construction uses the perp image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WeilOrthogonalGroupInvariance.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WeilOrthogonalGroupInvariance.lean#L26-L37

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

theorem GlobalTheory.CompanionTheory.SW.Core.OrthMeas.perp_image {V : Type} (χ : V → V → ℂ) (e : V ≃ V)
    (hχ : ∀ x y, χ (e x) (e y) = χ x y) (L : Set V) :
    perp χ (e '' L) = e '' perp χ L := by sorry
