-- Prove2me | Theorems.Thm_GlobalTheory_eulerProduct_ne_zero_one_of_entire
-- name    : GlobalTheory.eulerProduct_ne_zero_one_of_entire
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:25.714245+00:00
-- url     : https://prove2.me/theorems/a79bea88-3f3e-4378-ab7a-0589cdb66ca7
-- title:
--   Global Theory: euler Product ne zero one of entire
-- statement:
--   The Global Theory construction uses the euler Product ne zero one of entire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EulerProductNeZeroOneOfEntire.lean#L95-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EulerProductNeZeroOneOfEntire.lean#L95-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
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
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem GlobalTheory.eulerProduct_ne_zero_one_of_entire : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z L : ℂ → ℂ, Differentiable ℂ Z → Differentiable ℂ L → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → (∀ s : ℂ, 1 < s.re → L s = Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))) → L 1 ≠ 0 := by sorry
