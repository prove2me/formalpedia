-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_quantitative_headline
-- name    : MetricTesting.Characterization.Supplement.quantitative_headline
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:21:19.73461+00:00
-- url     : https://prove2.me/theorems/1016335c-2232-4607-88be-e80a2e4944cd
-- title:
--   Theorem 1.2 — Quantitative metric testing in all proximity regimes
-- statement:
--   Fix a real $C>2$ and $\epsilon_0=1/80$. With $F(n,\epsilon)$ as defined in the rate-function interface, for all sufficiently large $n$ and every $0<\epsilon\le\epsilon_0$:
--
--   1. On inputs in $[1,C]$, both one-sided and two-sided nonadaptive metric testing have complexity $\Theta_C(F(n,\epsilon))$.
--   2. Adaptive two-sided metric testing on $[1,C]$ has complexity $\Omega_C(\sqrt{n/\log n})$.
--   3. On arbitrary nonnegative symmetric inputs, nonadaptive and adaptive two-sided testing have respective lower bounds
--
--   $$\Omega(F(n,\epsilon)),\qquad \Omega(\sqrt{n/\log n}),$$
--
--   for positive metric targets and nonnegative pseudometric targets, and also for positive $\delta$-hyperbolic metric targets for each fixed real $\delta>0$.
--
--   All constants are positive and all integer thresholds precede $n$ and $\epsilon$. Bounded-range constants may depend on $C$; the hyperbolic transfer is quantified for each fixed $\delta$. This companion theorem records the full quantitative headline alongside the qualitative characterization.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: O, Ω and Θ query bounds with stated constant dependencies → positive existential constants and integer thresholds before every order and proximity, with ENNReal infima of feasible natural caps; reason: the discrete feasible caps have an attained least value when nonempty; the empty infimum is infinity
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 4, Theorem 1.2 (PDF p. 5); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_testing

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem quantitative_headline :
    (∀ C : ℝ, ∀ hC : 2 < C, ∃ c a b : ℝ, ∃ N : ℕ,
      0 < c ∧ 0 < a ∧ 0 < b ∧ 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1/80 →
        (∀ side : Bool,
          ENNReal.ofReal (c * rate n ε) ≤ Q (boundedProblem C (by linarith) false) n side true ε ∧
          Q (boundedProblem C (by linarith) false) n side true ε ≤ ENNReal.ofReal (a * rate n ε)) ∧
        ENNReal.ofReal (b * adaptiveRate n) ≤ Q (boundedProblem C (by linarith) false) n false false ε) ∧
    (∃ c a : ℝ, ∃ N : ℕ, 0 < c ∧ 0 < a ∧ 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1/80 →
        ∀ F ∈ ({positiveMetric, pseudoMetric} : Set LocalData),
          ENNReal.ofReal (c * rate n ε) ≤ Q (crossProblem NonnegativeValues F) n false true ε ∧
          ENNReal.ofReal (a * adaptiveRate n) ≤ Q (crossProblem NonnegativeValues F) n false false ε) ∧
    (∀ δ : ℝ, 0 < δ → ∃ c a : ℝ, ∃ N : ℕ, 0 < c ∧ 0 < a ∧ 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1/80 →
        ENNReal.ofReal (c * rate n ε) ≤ Q (localProblem (hyperbolic δ)) n false true ε ∧
        ENNReal.ofReal (a * adaptiveRate n) ≤ Q (localProblem (hyperbolic δ)) n false false ε) := by sorry

end MetricTesting.Characterization.Supplement
