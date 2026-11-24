-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_integrable_iteratedFDeriv
-- name    : GlobalTheory.SchwartzIntegralExchange.integrable_iteratedFDeriv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:48:04.626146+00:00
-- url     : https://prove2.me/theorems/688f3c97-381a-4090-9acf-f5bae763779f
-- title:
--   Schwartz Integral Exchange: integrable iterated FDeriv
-- statement:
--   The Schwartz Integral Exchange construction uses the integrable iterated FDeriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean#L87-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open GlobalTheory.SchwartzIntegralExchange
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {ν : Measure P} {Φ : P → SchwartzMap E ℂ} {c : P → ℂ}

theorem GlobalTheory.SchwartzIntegralExchange.integrable_iteratedFDeriv (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (n : ℕ) (x : E) : Integrable (fun ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x) ν := by sorry
