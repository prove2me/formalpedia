-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_fact_4_5
-- name    : MinimaxATE.Learnability.fact_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:00:21.915878+00:00
-- url     : https://prove2.me/theorems/458d8362-5643-4333-8c78-6a55155b563e
-- title:
--   Fact 4.5 — sums of independent variables with $\Pr[Z_j>z]\le e^{-z}$ are $\le C(J+\log 2/\eta)$ w.p. $1-\eta$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $Z_1,\dots,Z_J$ be independent nonnegative random variables on a probability space with
--   $$\Pr[Z_j>z]\le e^{-z}\qquad\text{for every }z\ge0\text{ and every }j .$$
--   Then for every $\eta\in(0,1)$, with probability at least $1-\eta$,
--   $$\sum_{j=1}^J Z_j\le C\,(J+\log(2/\eta)).$$
--
--   A corollary of Bernstein's inequality for sub-exponential variables; it controls the total confidence cost over the parts of the partition.
--
--   **Formalization Note.** Random variables are measurable real functions, independence is `iIndepFun`, and the conclusion bounds the probability of the failure event by $\eta$. $J=0$ is allowed (empty sum).
--
--   Differences from the source: none.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 24 (PDF 26), Fact 4.5

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MinimaxATE.Learnability

universe u

theorem fact_4_5 : ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (J : ℕ) (Z : Fin J → Ω → ℝ), (∀ j, Measurable (Z j)) → iIndepFun Z μ →
      (∀ j ω, 0 ≤ Z j ω) →
      (∀ j, ∀ z : ℝ, 0 ≤ z → μ {ω | z < Z j ω} ≤ ENNReal.ofReal (Real.exp (-z))) →
    ∀ (η : ℝ), 0 < η → η < 1 →
      μ {ω | C * ((J : ℝ) + Real.log (2 / η)) < ∑ j, Z j ω} ≤ ENNReal.ofReal η := by sorry

end MinimaxATE.Learnability
