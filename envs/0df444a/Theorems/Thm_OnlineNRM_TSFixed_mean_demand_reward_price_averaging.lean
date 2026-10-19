-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_mean_demand_reward_price_averaging
-- name    : OnlineNRM.TSFixed.mean_demand_reward_price_averaging
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T14:41:10.465304+00:00
-- url     : https://prove2.me/theorems/1d5db7ad-1c22-40b1-894f-77fd55db47f5
-- title:
--   Average the true mean reward over the conditional price draw
-- statement:
--   The expected true mean reward of the posted price equals the expected true-demand objective evaluated at the sampled selector. This is the price-randomization step, derived from `IsTSFixedRun.offer_price`; it does not replace realized demand or assume a regret formula.
--
--   Proof route: condition on pastSigma joined with the current posterior sample. For each k, the coefficient R_k = ∑ i, p i k * meanDemand F θ i k is measurable with respect to this sigma algebra because it contains the true parameter. Kernel-integral measurability and bounded demand make each coefficient bounded and integrable. Expand the match expression as ∑ k, R_k times the indicator of A t = some k. Apply the conditional-expectation pull-out property and `hrun.offer_price`, replacing the conditional indicator by xsel (θs t) k. Integrate using `integral_condExp`; the resulting finite sum is exactly lpObj. The remaining work is conditional-measurability and pull-out bookkeeping, independent of the demand-law extension in the other child.
--
--   The strict range t<T is preserved. The shut-off branch contributes zero; when K=0 both sides vanish. No positivity assumptions on inventory or consumption, or positive-horizon assumption, are needed.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.mean_demand_reward_price_averaging
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
    (∫ ω, (match A t ω with
      | none => 0
      | some k => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k) ∂P) =
      ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P := by sorry
