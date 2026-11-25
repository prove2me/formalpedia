-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_integrableOn_minor
-- name    : GlobalTheory.MinorInt.integrableOn_minor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:25.789785+00:00
-- url     : https://prove2.me/theorems/a20d1465-6aab-4dd5-9cc3-634875746fb9
-- title:
--   Minor Int: integrable On minor
-- statement:
--   The Minor Int construction uses the integrable On minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L463-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L463-L558

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

theorem GlobalTheory.MinorInt.integrableOn_minor (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hn : 2 * (Fintype.card ι + Fintype.card κ) ≤ n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ IntegrableOn
      (fun y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ => (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹)
      {y | ∀ a b, ‖((Matrix.of y)ᵀ * Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) *
        (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ)) a b‖
          < δ₀} volume := by sorry
