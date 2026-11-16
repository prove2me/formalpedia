-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_general_metric_lower_bounds
-- name    : MetricTesting.Characterization.Supplement.general_metric_lower_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:28:45.107451+00:00
-- url     : https://prove2.me/theorems/8315cdd9-7163-413f-bb97-932f9e855c2e
-- title:
--   Theorem 6.12 — Lower bounds for unrestricted metric testing
-- statement:
--   There are absolute positive constants $c,a$, an integer threshold $N\ge4$ and a positive bit constant $B$ such that, for all $n\ge N$ and $0<\epsilon\le1/80$, nonadaptive two-sided and adaptive two-sided testing on arbitrary nonnegative symmetric inputs require, respectively,
--
--   $$cF(n,\epsilon),\qquad a\sqrt{\frac n{\log n}}$$
--
--   queries. Both lower bounds hold for positive metric repair targets and nonnegative pseudometric repair targets. Each also holds with the success guarantee restricted to inputs whose reduced rational entries have numerator and denominator bit lengths at most $B(1+\lceil\log_2 n\rceil)$.
--
--   The constants and bit bound are independent of $n$ and $\epsilon$. This transfers both lower bounds to the unrestricted input setting without imposing triangle inequalities, positivity, a finite alphabet or rationality on all inputs.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: O, Ω and Θ query bounds with stated constant dependencies → positive existential constants and integer thresholds before every order and proximity, with ENNReal infima of feasible natural caps; reason: the discrete feasible caps have an attained least value when nonempty; the empty infimum is infinity
--   - encoding: hard inputs with O_C(log n)-bit rational entries (absolute in Theorem 6.12) → the lower bound also holds for the rational input promise with a uniform numerator and denominator bit bound; reason: the source hard distributions use only these finite alphabets; no upper-bound or general input restriction is added
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 31, Theorem 6.12 (PDF p. 32); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_testing

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem general_metric_lower_bounds :
    ∃ c a : ℝ, ∃ N B : ℕ, 0 < c ∧ 0 < a ∧ 4 ≤ N ∧ 0 < B ∧
      ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1/80 →
        ∀ F ∈ ({positiveMetric, pseudoMetric} : Set LocalData),
          ENNReal.ofReal (c * rate n ε) ≤ Q (crossProblem NonnegativeValues F) n false true ε ∧
          ENNReal.ofReal (a * adaptiveRate n) ≤ Q (crossProblem NonnegativeValues F) n false false ε ∧
          ENNReal.ofReal (c * rate n ε) ≤ rationalQ (crossProblem NonnegativeValues F) B n false true ε ∧
          ENNReal.ofReal (a * adaptiveRate n) ≤ rationalQ (crossProblem NonnegativeValues F) B n false false ε := by sorry

end MetricTesting.Characterization.Supplement
