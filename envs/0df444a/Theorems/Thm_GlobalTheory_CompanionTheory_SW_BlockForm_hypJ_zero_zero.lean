-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_zero_zero
-- name    : GlobalTheory.CompanionTheory.SW.BlockForm.hypJ_zero_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:17.719294+00:00
-- url     : https://prove2.me/theorems/d58448b8-d1b1-460a-8f04-4ebf8b250585
-- title:
--   Block Form: hyp J zero zero
-- statement:
--   The Block Form construction uses the hyp J zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L31-L32

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HyperbolicAndBlockOneNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockForm
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.BlockForm.hypJ_zero_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 0 = 0 := by sorry
