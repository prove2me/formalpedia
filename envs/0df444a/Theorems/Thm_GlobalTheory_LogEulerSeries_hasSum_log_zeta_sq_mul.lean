-- Prove2me | Theorems.Thm_GlobalTheory_LogEulerSeries_hasSum_log_zeta_sq_mul
-- name    : GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:50.033694+00:00
-- url     : https://prove2.me/theorems/5f666849-ea85-46ac-a6cd-02085c038180
-- title:
--   Log Euler Series: has Sum log zeta sq mul
-- statement:
--   The Log Euler Series construction uses the has Sum log zeta sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasSumLogZetaSqMul.lean#L63-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasSumLogZetaSqMul.lean#L63-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.LogEulerSeries

theorem GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → ∀ s : ℂ, 1 < s.re → HasSum (fun p : ι × ℕ => (((2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1) : ℝ) : ℂ) * Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s)) (2 * (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) + (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) + (∑' i, -Complex.log (1 - starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s)))) := by sorry
