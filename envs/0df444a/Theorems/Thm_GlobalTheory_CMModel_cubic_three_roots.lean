-- Prove2me | Theorems.Thm_GlobalTheory_CMModel_cubic_three_roots
-- name    : GlobalTheory.CMModel.cubic_three_roots
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:02:35.85357+00:00
-- url     : https://prove2.me/theorems/7322b97e-2ae2-4c3b-b0aa-25af1015988a
-- title:
--   CMModel: cubic three roots
-- statement:
--   The CMModel construction uses the cubic three roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CubicThreeRoots.lean#L5-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CubicThreeRoots.lean#L5-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CubicThreeRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMModel

theorem GlobalTheory.CMModel.cubic_three_roots (g h e₁ e₂ e₃ : ℂ) (h₁ : 4 * e₁ ^ 3 - g * e₁ - h = 0)
    (h₂ : 4 * e₂ ^ 3 - g * e₂ - h = 0) (h₃ : 4 * e₃ ^ 3 - g * e₃ - h = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧
      16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4))
        = -(g ^ 3 - 27 * h ^ 2) := by sorry
