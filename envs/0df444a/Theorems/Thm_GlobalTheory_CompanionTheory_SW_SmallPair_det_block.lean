-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_det_block
-- name    : GlobalTheory.CompanionTheory.SW.SmallPair.det_block
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:52.636075+00:00
-- url     : https://prove2.me/theorems/ed32630e-50c6-435b-923a-68d45ebcae93
-- title:
--   Small Pair: det block
-- statement:
--   The Small Pair construction uses the det block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L38-L41

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SmallPair

theorem GlobalTheory.CompanionTheory.SW.SmallPair.det_block (τ : ℂ) (h : 0 < τ.im) : (block τ).det = 1 := by sorry
