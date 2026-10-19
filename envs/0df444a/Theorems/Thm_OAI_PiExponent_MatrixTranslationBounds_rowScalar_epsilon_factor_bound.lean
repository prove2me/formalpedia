-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_epsilon_factor_bound
-- name    : OAI.PiExponent.MatrixTranslationBounds.rowScalar_epsilon_factor_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:57:44.216861+00:00
-- url     : https://prove2.me/theorems/3e6f673b-2f57-427e-b1dd-7cdebb9842e9
-- title:
--   Weighted majorant for the row epsilon factor
-- statement:
--   Bounds the epsilon product using the coordinate exponential controls. Natural exponents m i satisfy m i ≤ a i and their real casts satisfy m i ≥ a i - β i - d i. Positivity of C, ν, and the weights gives the stated bound, including coordinates where β i exceeds a i.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem OAI.PiExponent.MatrixTranslationBounds.rowScalar_epsilon_factor_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ)
    (C ν ws : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws)
    (hw : ∀ i, ws ≤ w i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖∏ i, ε i ^ (a i - β i - d i)‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        C * weight w (fun i => a i) / ws) := by sorry
