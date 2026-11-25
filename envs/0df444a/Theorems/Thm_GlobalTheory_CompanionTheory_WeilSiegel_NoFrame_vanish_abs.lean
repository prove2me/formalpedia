-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_NoFrame_vanish_abs
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.vanish_abs
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:41.276303+00:00
-- url     : https://prove2.me/theorems/2752dbc0-e42c-57fe-b157-9d82fef3497d
-- title:
--   No Frame: vanish abs
-- statement:
--   The No Frame construction uses the vanish abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableOfMulUnimodular.lean#L28-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableOfMulUnimodular.lean#L28-L94

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableOfMulUnimodular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.vanish_abs {X : Type} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] (e : X → X → ℂ)
    (he : ∀ z, Continuous fun v => e v z) (he' : ∀ v, Continuous fun z => e v z)
    (hen : ∀ a b, ‖e a b‖ = 1) (J : X → ℂ) (hJ : Integrable J μ) (N : Set X) (hN : IsOpen N)
    (hb : ∀ N' : Set X, IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : X → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, J v * e v z ∂μ) * Φ z ∂μ = 0) (z₀ : X) (hz : z₀ ∈ closure N) :
    ∫ v, J v * e v z₀ ∂μ = 0 := by sorry
