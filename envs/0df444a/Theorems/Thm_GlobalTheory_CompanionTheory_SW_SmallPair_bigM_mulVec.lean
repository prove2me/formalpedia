-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_bigM_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.SmallPair.bigM_mulVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:44.900982+00:00
-- url     : https://prove2.me/theorems/13a98e9f-046a-4154-af5f-ea49495a7231
-- title:
--   Small Pair: big M mul Vec
-- statement:
--   The Small Pair construction uses the big M mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L47-L52

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

theorem GlobalTheory.CompanionTheory.SW.SmallPair.bigM_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ)
    (v : Fin 2 × ι → ℝ) (k : Fin 2) (w : ι) :
    (bigM τ *ᵥ v) (k, w) = ∑ j, block (τ w) k j * v (j, w) := by sorry
