-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockOne_zero_succ
-- name    : GlobalTheory.CompanionTheory.SW.BlockForm.blockOne_zero_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:04.050671+00:00
-- url     : https://prove2.me/theorems/ecedb240-4c56-41ec-807d-a2c2a26f8852
-- title:
--   Block Form: block One zero succ
-- statement:
--   The Block Form construction uses the block One zero succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L14-L15

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

theorem GlobalTheory.CompanionTheory.SW.BlockForm.blockOne_zero_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : blockOne t A 0 j.succ = 0 := by sorry
