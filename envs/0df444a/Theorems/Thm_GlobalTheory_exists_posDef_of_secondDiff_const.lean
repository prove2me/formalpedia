-- Prove2me | Theorems.Thm_GlobalTheory_exists_posDef_of_secondDiff_const
-- name    : GlobalTheory.exists_posDef_of_secondDiff_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:12.341301+00:00
-- url     : https://prove2.me/theorems/7fcc3c4d-9827-4810-a3bf-e56e7cd10b90
-- title:
--   Global Theory: exists pos Def of second Diff const
-- statement:
--   The Global Theory construction uses the exists pos Def of second Diff const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L393-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L393-L410

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]

theorem GlobalTheory.exists_posDef_of_secondDiff_const [Module.Free ℤ X] [Module.Finite ℤ X] (f : X → ℝ)
    (h : ∀ a a' μ ν : X, f (a + μ + ν) - f (a + μ) - f (a + ν) + f a =
      f (a' + μ + ν) - f (a' + μ) - f (a' + ν) + f a')
    (he : ∀ x, f (-x) = f x) (ht : Tendsto f cofinite atTop) :
    ∃ (B : X →+ X →+ ℝ) (Q : QuadraticForm ℝ (ℝ ⊗[ℤ] X)),
      (∀ a μ ν, B μ ν = f (a + μ + ν) - f (a + μ) - f (a + ν) + f a) ∧
      (∀ μ ν, B μ ν = B ν μ) ∧ (∀ x, f x - f 0 = B x x / 2) ∧ (∀ x, x ≠ 0 → 0 < f x - f 0) ∧
      Q.PosDef ∧ (∀ x, Q (1 ⊗ₜ x) = f x - f 0) ∧
      ∀ μ ν, QuadraticMap.polar Q (1 ⊗ₜ μ) (1 ⊗ₜ ν) = B μ ν := by sorry
