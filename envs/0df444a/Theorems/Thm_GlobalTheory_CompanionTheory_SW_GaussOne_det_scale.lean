-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussOne_det_scale
-- name    : GlobalTheory.CompanionTheory.SW.GaussOne.det_scale
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:50.695806+00:00
-- url     : https://prove2.me/theorems/ce9b2f94-54ba-4429-94f9-f928fe13c9f8
-- title:
--   Gauss One: det scale
-- statement:
--   The Gauss One construction uses the det scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RealGaussianFourierTransform.lean#L107-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RealGaussianFourierTransform.lean#L107-L120

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussOne
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.GaussOne.det_scale {g S : Matrix ι ι ℝ} {e : ι → ℝ} (he : ∀ i, e i = 1 ∨ e i = -1)
    (hS : gᵀ * S * g = Matrix.diagonal e) : Real.sqrt |S.det| * |g.det| = 1 := by sorry
