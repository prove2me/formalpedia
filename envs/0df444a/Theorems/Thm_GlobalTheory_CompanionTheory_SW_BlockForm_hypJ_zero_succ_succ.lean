-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_zero_succ_succ
-- name    : GlobalTheory.CompanionTheory.SW.BlockForm.hypJ_zero_succ_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:00.948659+00:00
-- url     : https://prove2.me/theorems/a681f241-a858-4675-acca-d837f27714a1
-- title:
--   Block Form: hyp J zero succ succ
-- statement:
--   The Block Form construction uses the hyp J zero succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L38-L39

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

theorem GlobalTheory.CompanionTheory.SW.BlockForm.hypJ_zero_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 0 j.succ.succ = 0 := by sorry
