-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_generic_product_bound
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.generic_product_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:28:52.946243+00:00
-- url     : https://prove2.me/theorems/94d2e90e-deca-404a-a23a-05bac3f0a637
-- title:
--   Combine scalar and determinant estimates through weighted occupancy
-- statement:
--   For arbitrary finite row and index types, a low-weight capacity bound and a total-weight lower bound combine separate exponential estimates into the maximum of a collision rate and an approximation rate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.generic_product_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) (scalar determinant : ℂ)
    {H A eta nu c N bbar Etr Ehol rho : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N)
    (hweight : ∀ a, 0 ≤ weight a)
    (hmean : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i : ι, weight (group i))
    (hcapacity : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N)
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
