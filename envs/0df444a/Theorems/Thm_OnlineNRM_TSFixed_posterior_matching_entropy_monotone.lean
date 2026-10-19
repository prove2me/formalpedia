-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_entropy_monotone
-- name    : OnlineNRM.TSFixed.posterior_matching_entropy_monotone
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T15:00:41.41892+00:00
-- url     : https://prove2.me/theorems/d17179e8-ba82-4d91-8a69-ce222c1375b6
-- title:
--   Posterior oracle entropy decreases when the current history is observed
-- statement:
--   For a measurable selector with nonnegative weights summing to at most one, adjoining shut-off gives a probability distribution on the finite oracle action set. Its expected conditional entropy cannot increase when the current action and demand are added to the history.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.posterior_matching_entropy_monotone
    {N K : ℕ}
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (xsel : Θ → Fin K → ℝ) (t : ℕ)
    (hθ : Measurable θ) (hx : Measurable xsel)
    (hx0 : ∀ ρ k, 0 ≤ xsel ρ k)
    (hx1 : ∀ ρ, ∑ k : Fin K, xsel ρ k ≤ 1) :
    0 ≤ finitePosteriorEntropy P (histSigma A D t)
        (fun ω a => oracleActionWeights xsel (θ ω) a) -
      finitePosteriorEntropy P (histSigma A D (t + 1))
        (fun ω a => oracleActionWeights xsel (θ ω) a) := by sorry
