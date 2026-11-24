-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_succ_succ_one
-- name    : GlobalTheory.CompanionTheory.SW.BlockForm.hypJ_succ_succ_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:58.952798+00:00
-- url     : https://prove2.me/theorems/57c8f1cf-c9b3-4a43-98f5-a083fd74c7f5
-- title:
--   Block Form: hyp J succ succ one
-- statement:
--   The Block Form construction uses the hyp J succ succ one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L56-L58

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

theorem GlobalTheory.CompanionTheory.SW.BlockForm.hypJ_succ_succ_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 1 = 0 := by sorry
