-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Mobius_im_frac
-- name    : GlobalTheory.CompanionTheory.SW.Core.Mobius.im_frac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:18.682384+00:00
-- url     : https://prove2.me/theorems/634a8f9f-605e-454b-80b6-c6286f51957e
-- title:
--   Mobius: im frac
-- statement:
--   The Mobius construction uses the im frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MobiusActionUpperHalfPlane.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MobiusActionUpperHalfPlane.lean#L22-L27

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MobiusActionUpperHalfPlane
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Mobius

theorem GlobalTheory.CompanionTheory.SW.Core.Mobius.im_frac (a b c d : ℝ) (hdet : a * d - b * c = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a : ℂ) * τ + b) / ((c : ℂ) * τ + d)).im = τ.im / ‖(c : ℂ) * τ + d‖ ^ 2 := by sorry
