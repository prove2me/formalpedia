-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_logTail_product_coefficient_control_generic_product
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_generic_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:16:16.212733+00:00
-- url     : https://prove2.me/theorems/9f40131c-86fc-49ff-89b4-61af6619764b
-- title:
--   Coefficient control for products with prescribed minimum degrees
-- statement:
--   For finitely many complex power series whose coefficients have norm at most one and whose coefficients vanish below positive degrees T i, the coefficient at degree k of the product of their powers has norm at most 2^k. A nonzero coefficient implies that the sum of the minimum degrees, counted according to the powers, is at most k.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.logTail_product_coefficient_control_generic_product
    {m : ℕ} (f : Fin m → PowerSeries ℂ) (T b : Fin m → ℕ) (k : ℕ)
    (hT : ∀ i, 1 ≤ T i)
    (hsupp : ∀ i n, n < T i → PowerSeries.coeff n (f i) = 0)
    (hcoeff : ∀ i n, ‖PowerSeries.coeff n (f i)‖ ≤ 1) :
    ‖PowerSeries.coeff k (∏ i : Fin m, (f i) ^ b i)‖ ≤ (2 : ℝ) ^ k ∧
    (PowerSeries.coeff k (∏ i : Fin m, (f i) ^ b i) ≠ 0 →
      ∑ i : Fin m, T i * b i ≤ k) := by sorry
