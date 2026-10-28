-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_full_demand_period_mean_replacement
-- name    : OnlineNRM.TSFixed.full_demand_period_mean_replacement
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T14:39:51.924102+00:00
-- url     : https://prove2.me/theorems/4a1f92a0-b136-4f63-999d-96ec4c3c001b
-- title:
--   Replace realized full demand by its conditional mean in period revenue
-- statement:
--   In every period t<T, full-demand revenue is integrable, and its expectation equals the true mean reward of the posted price. This is the demand-conditioning step, derived from `IsTSFixedRun.demand`, rather than the regret identity.
--
--   Proof route: condition on pastSigma joined with the current posterior sample and posted price. This sigma algebra lies below the ambient measurable space and makes the true parameter and posted price measurable. First apply the event-law assumption to the common measurable box |x i| ≤ |dbar i|, which includes zero and has probability one under every demandLaw. This gives almost-sure bounds on realized demand and integrability of period revenue. Extend the conditional event identity by linearity from indicators to simple functions and then by dominated approximation to bounded coordinate truncations. Those truncations agree almost surely with the coordinates under both realized demand and demandLaw. Consequently the conditional coordinate mean is meanDemand for `some k`, and zero for `none`. Pull out the measurable posted prices, sum over products, and apply `integral_condExp`.
--
--   The unresolved core here is the indicator-to-bounded-function extension. No price-averaging identity is assumed. The strict hypothesis t<T is retained; at zero horizon it is impossible. Empty product sets and shut-off prices give zero revenue, and signed consumption or inventory play no role.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.full_demand_period_mean_replacement
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
    Integrable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) P ∧
      (∫ ω, ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i ∂P) =
        ∫ ω, (match A t ω with
          | none => 0
          | some k => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k) ∂P := by sorry
