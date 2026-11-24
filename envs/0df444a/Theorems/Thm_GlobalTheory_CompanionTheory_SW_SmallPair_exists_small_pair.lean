-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_exists_small_pair
-- name    : GlobalTheory.CompanionTheory.SW.SmallPair.exists_small_pair
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:39.752671+00:00
-- url     : https://prove2.me/theorems/c9a7ec8c-933b-43a4-8015-702b443033ca
-- title:
--   Small Pair: exists small pair
-- statement:
--   The Small Pair construction uses the exists small pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L153-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L153-L207

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

theorem GlobalTheory.CompanionTheory.SW.SmallPair.exists_small_pair : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) ∧
      ∀ w, ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)‖ ^ 2 ≤ C * (τ w).im := by sorry
