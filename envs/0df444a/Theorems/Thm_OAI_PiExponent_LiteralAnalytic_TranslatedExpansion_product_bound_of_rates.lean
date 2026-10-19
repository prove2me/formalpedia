-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_product_bound_of_rates
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.product_bound_of_rates
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:41:12.597335+00:00
-- url     : https://prove2.me/theorems/6c5604cf-ae40-4764-aba8-834440f3d758
-- title:
--   Combine product estimates from either rate bound
-- statement:
--   Under the scalar and determinant exponential estimates, the mean lower bound, and either alternative of the occupancy dichotomy, the product norm is bounded by the exponential with the maximum of the collision and approximation rates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.product_bound_of_rates
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) (scalar determinant : ℂ)
    {H A eta nu c N bbar Etr Ehol rho : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N)
    (hmean : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i : ι, weight (group i))
    (hcoll : 0 ≤ ∑ a : κ,
      (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2)
    (hrates : (eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤
      ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2) ∨
      ((Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
      (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar))
    (hscalar : ‖scalar‖ ≤ Real.exp
      (-nu * ((∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) +
        (Fintype.card ι : ℝ) * H * Etr))
    (hdet : ‖determinant‖ ≤ Real.exp
      (-c * (∑ a : κ,
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H * (Ehol + rho))) :
    ‖scalar * determinant‖ ≤ Real.exp ((Fintype.card ι : ℝ) * H *
      (Etr + Ehol + rho + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar)))) := by sorry
