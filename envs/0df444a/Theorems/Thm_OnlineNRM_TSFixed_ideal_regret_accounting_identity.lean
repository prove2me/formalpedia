-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_ideal_regret_accounting_identity
-- name    : OnlineNRM.TSFixed.ideal_regret_accounting_identity
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T14:28:56.547113+00:00
-- url     : https://prove2.me/theorems/5f800914-ac8c-4376-977e-4e65e1916a67
-- title:
--   Exact decomposition of full-demand LP regret into selector reward gaps
-- statement:
--   For a TS-fixed run, expected LP benchmark times T minus expected full-demand revenue equals the sum of expected true-demand objective gaps between the true-parameter LP selector and each sampled-parameter selector. This is an exact accounting identity valid also at zero horizon.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.ideal_regret_accounting_identity
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
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel) :
    (∫ ω, lpOpt p a (meanDemand F (θ ω)) (fun j => I j / (T : ℝ)) ∂P) *
        (T : ℝ) - ∫ ω, revenue p A D T ω ∂P =
      ∑ t ∈ Finset.range T,
        ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
          lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P := by sorry
