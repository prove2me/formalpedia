-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_columns_integral
-- name    : GlobalTheory.MinorInt.columns_integral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:25:31.082692+00:00
-- url     : https://prove2.me/theorems/48cd00f8-1f47-427e-b8ac-74022bca3e1b
-- title:
--   Minor Int: columns integral
-- statement:
--   The Minor Int construction uses the columns integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L266-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L266-L420

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt

theorem GlobalTheory.MinorInt.columns_integral (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hn : 2 * (Fintype.card ι + Fintype.card κ) ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∫⁻ x : (ι → ι → ℂ) × (κ → ι → ℂ),
      {x : (ι → ι → ℂ) × (κ → ι → ℂ) | ∀ i j, ‖((Matrix.of x.1)ᵀᴴ * (Matrix.of x.1)ᵀ -
        (Matrix.of x.2)ᴴ * Matrix.of x.2 - 1 : Matrix ι ι ℂ) i j‖ < δ}.indicator
        (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ n)⁻¹) x < ⊤ := by sorry
