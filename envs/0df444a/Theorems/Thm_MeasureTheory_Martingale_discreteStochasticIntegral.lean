-- Prove2me | Theorems.Thm_MeasureTheory_Martingale_discreteStochasticIntegral
-- name    : MeasureTheory.Martingale.discreteStochasticIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:44.736591+00:00
-- url     : https://prove2.me/theorems/e213227a-3975-5a8b-9add-55a19cc05367
-- title:
--   Predictable discrete stochastic integrals preserve martingales
-- statement:
--   A discrete stochastic integral of a martingale against a strongly predictable integrand with an almost surely bounded value at each time is a martingale.
-- source:
--   StochLean.Probability.Martingale.DiscreteIntegral

import Definitions.Def_SourceProof_eae059fb1d843e68f8ce3b08

open MeasureTheory
open scoped BigOperators

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → ℝ} {X : ℕ → Ω → E}

theorem MeasureTheory.Martingale.discreteStochasticIntegral [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (hH : IsStronglyPredictable 𝓕 H)
    (hH_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂μ, ‖H n ω‖ ≤ C) :
    Martingale (MeasureTheory.discreteStochasticIntegral H X) 𝓕 μ := by sorry
