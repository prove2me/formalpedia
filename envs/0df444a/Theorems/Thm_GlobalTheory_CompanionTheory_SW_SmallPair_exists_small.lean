-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_exists_small
-- name    : GlobalTheory.CompanionTheory.SW.SmallPair.exists_small
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:41.999834+00:00
-- url     : https://prove2.me/theorems/fec2829c-34a6-41ed-9235-341602bd078f
-- title:
--   Small Pair: exists small
-- statement:
--   The Small Pair construction uses the exists small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L58-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L58-L151

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

theorem GlobalTheory.CompanionTheory.SW.SmallPair.exists_small {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ]
    [Nonempty ι]
    (b : Module.Basis κ ℝ (ι → ℝ)) (S : AddSubgroup (ι → ℝ)) (hS : ∀ i, b i ∈ S) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ τ : ι → ℂ, (∀ w, 0 < (τ w).im) →
      ∃ u ∈ S, ∃ v ∈ S, (u ≠ 0 ∨ v ≠ 0) ∧ ∀ w,
        |√(τ w).im * u w| ≤ R ∧ |(τ w).re / √(τ w).im * u w + 1 / √(τ w).im * v w| ≤ R := by sorry
