-- Prove2me | Theorems.Thm_KendallQueues_GIMs_mms_lambda_eq_rho
-- name    : KendallQueues.GIMs.mms_lambda_eq_rho
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:23.460982+00:00
-- url     : https://prove2.me/theorems/73db1bff-a623-4063-8a6c-07a0927312ab
-- title:
--   §8, p. 350, eq. (27) — for M/M/s the λ-equation is λ² − (1 + ρ)λ + ρ = 0, with root λ = ρ
-- statement:
--   Consider M/M/s: $s\ge1$ servers, Poissonian input with negative-exponential inter-arrival times of mean $a>0$ (law $dA(u)=a^{-1}e^{-u/a}du$ on $u\ge0$), and exponential service of mean $b>0$, with $\rho=b/(sa)<1$. Let $F(x)=\int_0^\infty e^{-(1-x)su/b}\,dA(u)$. Then for $0<x<1$,
--   $$F(x)=x\iff x^2-(1+\rho)x+\rho=0,$$
--   and the root in the interval $(0,1)$ is $\lambda=\rho$: $0<\rho<1$ and $F(\rho)=\rho$.
--
--   This identifies $\lambda$ in the classical Erlang case, where the results are well known.
--
--   **Formalization Note** The exponential law of mean $a$ is Mathlib's `expMeasure` with rate $a^{-1}$.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §8, p. 350, eq. (27)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

open ProbabilityTheory

/-- §8, p. 350, eq. (27): for Poissonian input (M/M/s), with inter-arrival law exponential of
mean `a`, the `λ`-equation `F(λ) = λ` on `(0, 1)` is `λ² - (1 + ρ)λ + ρ = 0`, and its root in
`(0, 1)` is `λ = ρ`. -/
theorem mms_lambda_eq_rho (s : ℕ) (hs : 1 ≤ s) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hρ : rho s a b < 1) :
    (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
      (F s (expMeasure a⁻¹) b x = x ↔ x ^ 2 - (1 + rho s a b) * x + rho s a b = 0)) ∧
      rho s a b ∈ Set.Ioo (0 : ℝ) 1 ∧ F s (expMeasure a⁻¹) b (rho s a b) = rho s a b := by sorry

end KendallQueues.GIMs
