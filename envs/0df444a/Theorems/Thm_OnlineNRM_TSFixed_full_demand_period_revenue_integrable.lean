-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_full_demand_period_revenue_integrable
-- name    : OnlineNRM.TSFixed.full_demand_period_revenue_integrable
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T14:46:39.074969+00:00
-- url     : https://prove2.me/theorems/4200b95e-e6f5-4b61-a9b7-af5bc0890bd9
-- title:
--   Integrability of full-demand revenue in one period
-- statement:
--   For each period covered by the run, realized full-demand revenue is integrable. A proof transfers the kernel’s almost-sure coordinate bounds to the realized demand using the run’s conditional event law, then uses the finite price and product indices.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.full_demand_period_revenue_integrable
    {N M K T : ℕ}
    (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ)
    (I : Fin M → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K))
    (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel)
    (t : ℕ) (ht : t < T) :
    Integrable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) P := by sorry
