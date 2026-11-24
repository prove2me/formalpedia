-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLSmall_tendsto_zero_of_le_pow
-- name    : GlobalTheory.CompanionTheory.GLSmall.tendsto_zero_of_le_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:16.81822+00:00
-- url     : https://prove2.me/theorems/965a2e36-29a0-450e-bd29-8fad163b0bb8
-- title:
--   GLSmall: tendsto zero of le pow
-- statement:
--   The GLSmall construction uses the tendsto zero of le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLevelInverseCongruence.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLevelInverseCongruence.lean#L18-L27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLSmall
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.GLSmall.tendsto_zero_of_le_pow {ϖ : k} (h : valuation k ϖ < 1) {α : Type} {s : ℕ → Set α} (f : α → k)
    (hf : ∀ l, ∀ a ∈ s l, valuation k (f a) ≤ valuation k ϖ ^ l) :
    Tendsto f (⨅ l, 𝓟 (s l)) (𝓝 0) := by sorry
