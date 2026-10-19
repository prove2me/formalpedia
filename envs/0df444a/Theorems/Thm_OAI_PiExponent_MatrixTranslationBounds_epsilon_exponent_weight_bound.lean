-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_epsilon_exponent_weight_bound
-- name    : OAI.PiExponent.MatrixTranslationBounds.epsilon_exponent_weight_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:15:47.524299+00:00
-- url     : https://prove2.me/theorems/9f59ada1-55fd-4b8a-9ba4-8881717e9fd0
-- title:
--   Convert the epsilon exponent to a weighted majorant
-- statement:
--   Bounds the sum of the coordinate exponent contributions by the target weighted expression, including coordinates where β exceeds a.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.epsilon_exponent_weight_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ)
    (C ν ws : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws)
    (hw : ∀ i, ws ≤ w i) :
    (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) ≤
      -ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        C * weight w (fun i => a i) / ws := by sorry
