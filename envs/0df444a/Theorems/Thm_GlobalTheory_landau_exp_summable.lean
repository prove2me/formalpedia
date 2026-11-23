-- Prove2me | Theorems.Thm_GlobalTheory_landau_exp_summable
-- name    : GlobalTheory.landau_exp_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:46.275824+00:00
-- url     : https://prove2.me/theorems/9d9467b7-06c2-4296-9b9c-d47b0ee82e28
-- title:
--   Global Theory: landau exp summable
-- statement:
--   The Global Theory construction uses the landau exp summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LandauSummableOfExpDirichletSeriesEntire.lean#L84-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LandauSummableOfExpDirichletSeriesEntire.lean#L84-L293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
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

theorem GlobalTheory.landau_exp_summable : ∀ (ι : Type) (a l : ι → ℝ) (F : ℂ → ℂ),
    (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ l i) → Differentiable ℂ F →
    (∀ s : ℂ, 1 < s.re → ∃ g : ℂ, HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * s)) g ∧
      F s = Complex.exp g) → Summable a := by sorry
