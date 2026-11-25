-- Prove2me | Theorems.Thm_GlobalTheory_log_exp_mul_le_of_generator_sup_bound
-- name    : GlobalTheory.log_exp_mul_le_of_generator_sup_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:23.318017+00:00
-- url     : https://prove2.me/theorems/8bc58548-585f-4123-943e-661de1bd1302
-- title:
--   Global Theory: log exp mul le of generator sup bound
-- statement:
--   The Global Theory construction uses the log exp mul le of generator sup bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LogExpMulLeOfGeneratorSupBound.lean#L16-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LogExpMulLeOfGeneratorSupBound.lean#L16-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LogExpMulLeOfGeneratorSupBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 800000

theorem GlobalTheory.log_exp_mul_le_of_generator_sup_bound : ∀ (f r n d : ℕ) (L ℓ a rd lam t c S v p1 : ℝ), 2 ≤ L → 1 ≤ f → 1 ≤ r → r ≤ n → (d : ℝ) ≤ a → Real.log (1 + a) ≤ 2 * L → Real.log n ≤ L → Real.log f ≤ 2 * L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < lam → Real.log (1 / lam ^ 2) ≤ 80 * L → 0 < t → 0 ≤ ℓ → 0 ≤ p1 → p1 ≤ Real.exp ℓ → 0 ≤ c → c ≤ Real.exp (f * r * n * L) → 0 ≤ S → S ≤ 2 * v → v ≤ c * (p1 * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (f * r : ℕ) * n) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) / (Real.sqrt Real.pi * lam)) ^ (f * r * n)) → Real.log (Real.exp (-((d : ℝ) / 2) * Real.log (Real.pi * t)) * S) ≤ ℓ + 10 * L * a + 200 * f * r * n * L := by sorry
