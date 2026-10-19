-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_tsFixed_ideal_reward_regret_le
-- name    : OnlineNRM.TSFixed.tsFixed_ideal_reward_regret_le
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T14:13:18.99797+00:00
-- url     : https://prove2.me/theorems/32865fbe-e533-4a05-b1b3-6c5b63c94016
-- title:
--   TS-fixed LP regret against full-demand revenue
-- statement:
--   The expected LP benchmark multiplied by T exceeds expected revenue computed from full demand by at most 18 pmax times sqrt(T K log K), for every TS-fixed run satisfying the target hypotheses.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem OnlineNRM.TSFixed.tsFixed_ideal_reward_regret_le {N M K T : ℕ} (hK : 2 ≤ K) (hT : 1 ≤ T)
    (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ) (I : Fin M → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k) (ha : ∀ i j, 0 ≤ a i j) (hI : ∀ j, 0 ≤ I j)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ) (A : ℕ → Ω → Option (Fin K))
    (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel) :
    (∫ ω, lpOpt p a (meanDemand F (θ ω)) (fun j => I j / (T : ℝ)) ∂P) * (T : ℝ) -
        ∫ ω, revenue p A D T ω ∂P ≤
      18 * pmax p dbar * Real.sqrt ((T : ℝ) * K * Real.log K) := by sorry
