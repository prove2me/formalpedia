-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_full_demand_period_mean_replacement_identity
-- name    : OnlineNRM.TSFixed.full_demand_period_mean_replacement_identity
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T14:47:03.483602+00:00
-- url     : https://prove2.me/theorems/ab3bbc19-0a42-4d1d-b6f6-1f479b20c921
-- title:
--   Conditional mean identity for full-demand period revenue
-- statement:
--   The expected full-demand revenue in a period equals the expected posted-price mean reward. The independent proof route is to extend the run’s conditional event identity from indicators to bounded coordinate functions, identify their conditional means under each posted price (including the zero-demand shut-off case), and integrate after pulling out the measurable posted prices. This child contains the main unresolved mathematical obligation.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.full_demand_period_mean_replacement_identity
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
    (∫ ω, ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i ∂P) =
      ∫ ω, (match A t ω with
        | none => 0
        | some k => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k) ∂P := by sorry
