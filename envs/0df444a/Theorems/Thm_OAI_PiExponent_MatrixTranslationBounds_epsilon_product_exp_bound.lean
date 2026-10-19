-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_epsilon_product_exp_bound
-- name    : OAI.PiExponent.MatrixTranslationBounds.epsilon_product_exp_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:15:20.427294+00:00
-- url     : https://prove2.me/theorems/33e8d441-0f98-4a4e-b62b-94b5e968360f
-- title:
--   Exponential bound for the epsilon product
-- statement:
--   Bounds the norm of the finite epsilon product by the exponential of the sum of its coordinate exponents multiplied by their coordinate bounds.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.MatrixTranslationBounds.epsilon_product_exp_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ) (C ν : ℝ)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖∏ i, ε i ^ (a i - β i - d i)‖ ≤
      Real.exp (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) := by sorry
