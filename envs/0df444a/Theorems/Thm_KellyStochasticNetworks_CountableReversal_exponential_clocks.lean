-- Prove2me | Theorems.Thm_KellyStochasticNetworks_CountableReversal_exponential_clocks
-- name    : KellyStochasticNetworks.CountableReversal.exponential_clocks
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:49.170917+00:00
-- url     : https://prove2.me/theorems/781cd664-31d8-4d47-8099-a845e9d7e5f7
-- title:
--   Exercise 1.1 — memorylessness and competing exponential clocks
-- statement:
--   Let $P$ be a probability measure and $S$ a measurable real random variable with exponential distribution of rate $\lambda>0$. For every $s,t>0$,
--   $$
--   P(S>s+t\mid S>t)=P(S>s).
--   $$
--   Furthermore, for any measurable random variable $T$ independent of $S$ and exponentially distributed with rate $\mu>0$,
--   $$
--   \min\{S,T\}\sim\operatorname{Exp}(\lambda+\mu).
--   $$
--   These are the holding-time identities used to describe continuous-time jumps and competing clocks.
--
--   **Formalization Note** Exponential laws are Mathlib's probability measures `expMeasure`. The conditional survival probability is a ratio of real event probabilities; its denominator is strictly positive for every finite positive $t$. Independence of $T$ is required only for the second clause.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 16 (PDF p. 24), Exercise 1.1; https://doi.org/10.1017/CBO9781139565363

import Mathlib

open MeasureTheory ProbabilityTheory

namespace KellyStochasticNetworks.CountableReversal

theorem exponential_clocks {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (hS : Measurable S) (lam : ℝ) (hlam : 0 < lam)
    (hSlaw : P.map S = expMeasure lam) :
    (∀ s t : ℝ, 0 < s → 0 < t →
      (P {ω | s + t < S ω}).toReal / (P {ω | t < S ω}).toReal =
        (P {ω | s < S ω}).toReal) ∧
    (∀ (T : Ω → ℝ) (μ : ℝ), Measurable T → 0 < μ →
      P.map T = expMeasure μ → IndepFun S T P →
      P.map (fun ω => min (S ω) (T ω)) = expMeasure (lam + μ)) := by sorry

end KellyStochasticNetworks.CountableReversal
