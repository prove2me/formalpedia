-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_full_demand_period_revenue_integrable_of_bounds
-- name    : OnlineNRM.TSFixed.full_demand_period_revenue_integrable_of_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T18:08:31.559862+00:00
-- url     : https://prove2.me/theorems/c41418df-ae45-4141-aa32-4bee582ee2a7
-- title:
--   Integrability from active-price demand bounds
-- statement:
--   Measurable action and demand with almost-everywhere coordinate bounds on active-price events yield integrable one-period revenue. Bound its absolute value by the finite constant Σ_i |dbar i| Σ_k |p i k| and use integrable domination. Shut-off revenue and empty-index sums are zero.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.full_demand_period_revenue_integrable_of_bounds
    {N K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (t : ℕ) (hp : ∀ i k, 0 ≤ p i k)
    (hA : Measurable (A t)) (hD : Measurable (D t))
    (hbound : ∀ᵐ ω ∂P, A t ω = none ∨ ∀ i, D t ω i ∈ Set.Icc 0 (dbar i)) :
    Integrable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) P := by sorry
