-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_full_demand_period_demand_ae
-- name    : OnlineNRM.TSFixed.full_demand_period_demand_ae
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T18:08:07.554652+00:00
-- url     : https://prove2.me/theorems/077c65b1-8168-4479-95f9-53f12dc2ce02
-- title:
--   Almost-sure bounds for active-price demand
-- statement:
--   For a period within the run, full demand almost surely satisfies every coordinate bound whenever an active price is posted. Prove this from the run's conditional event law by integrating the out-of-bounds indicator over each measurable active-price event, then taking a finite union. Shut-off actions require no coordinate bound.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.full_demand_period_demand_ae
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
    ∀ᵐ ω ∂P, A t ω = none ∨ ∀ i, D t ω i ∈ Set.Icc 0 (dbar i) := by sorry
