-- Prove2me | Theorems.Thm_GlobalTheory_eulerProduct_eq_exp_and_pos
-- name    : GlobalTheory.eulerProduct_eq_exp_and_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:14.008792+00:00
-- url     : https://prove2.me/theorems/e99cadfc-414a-48ef-ae27-a7dec623b588
-- title:
--   Global Theory: euler Product eq exp and pos
-- statement:
--   The Global Theory construction uses the euler Product eq exp and pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/OneSubRePosOfNormLeHalf.lean#L30-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/OneSubRePosOfNormLeHalf.lean#L30-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_OneSubRePosOfNormLeHalf
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

theorem GlobalTheory.eulerProduct_eq_exp_and_pos :
    ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → (∀ s : ℂ, 1 < s.re → Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) ∧ HasProd (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))))) ∧ ∀ e : ι ≃ ι, (∀ i, N (e i) = N i) → (∀ i, c (e i) = starRingEnd ℂ (c i)) → ∀ s : ℂ, 1 < s.re → s.im = 0 → (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).im = 0 ∧ 0 < (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).re := by sorry
