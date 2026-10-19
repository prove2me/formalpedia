-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_logTail_product_coefficient_control
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T03:00:43.541291+00:00
-- url     : https://prove2.me/theorems/506ad75d-1a3d-4d66-bbd0-430794b64b51
-- title:
--   Coefficient norm and cutoff for products of logarithmic tails
-- statement:
--   For positive truncation orders, every degree-k coefficient of a product of logarithmic tails has norm at most 2^k. A nonzero coefficient forces the sum of truncation orders, counted with multiplicity, to be at most k. Prove the norm bound by counting positive-degree compositions and the cutoff by power-series order. This includes empty products and k = 0, and permits equality at the cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control
    {m : ℕ} (T b : Fin m → ℕ) (k : ℕ) (hT : ∀ i, 1 ≤ T i) :
    ‖PowerSeries.coeff k
      (∏ i : Fin m,
        ((PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ) ^ b i)‖ ≤ (2 : ℝ) ^ k ∧
    (PowerSeries.coeff k
      (∏ i : Fin m,
        ((PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ) ^ b i) ≠ 0 →
      ∑ i : Fin m, T i * b i ≤ k) := by sorry
