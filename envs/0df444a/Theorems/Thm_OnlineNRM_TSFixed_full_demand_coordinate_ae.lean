-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_full_demand_coordinate_ae
-- name    : OnlineNRM.TSFixed.full_demand_coordinate_ae
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T18:14:54.323555+00:00
-- url     : https://prove2.me/theorems/e3672908-46c1-4ae9-89d2-e0c145f7a1b8
-- title:
--   Almost-sure coordinate bound for active-price demand
-- statement:
--   For any period in a TS-fixed run and any demand coordinate, that coordinate lies within its prescribed bounds almost surely whenever an active price is posted. The shut-off action is exempt. This follows by transferring the conditional demand-law support bound to the event of each active price and taking a finite union over prices.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.full_demand_coordinate_ae
    {N M K T : ℕ}
    (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ)
    (I : Fin M → ℝ) (dbar : Fin N → ℝ)
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
    (t : ℕ) (ht : t < T) (i : Fin N) :
    ∀ᵐ ω ∂P, A t ω = none ∨ D t ω i ∈ Set.Icc 0 (dbar i) := by sorry
