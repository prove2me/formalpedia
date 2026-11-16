-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_adaptive_bounded_range_lower_bound
-- name    : MetricTesting.Characterization.Supplement.adaptive_bounded_range_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:28:07.942095+00:00
-- url     : https://prove2.me/theorems/cd5efa07-c29d-457a-8c7f-a4c60f146781
-- title:
--   Theorem 6.11 — Adaptive bounded-range lower bound
-- statement:
--   For every fixed real $C>2$, there exist $c_C>0$, $N_C\ge3$ and a positive bit constant $B_C$, uniform over $n$ and $\epsilon$, such that for all $n\ge N_C$ and $0<\epsilon\le1/80$, adaptive two-sided and adaptive one-sided metric testing on $[1,C]$ both require
--
--   $$c_C\sqrt{\frac n{\log n}}$$
--
--   queries. The assertion holds for bounded repairs and arbitrary positive metric repairs. It still holds when testing success is required only on inputs with reduced rational numerator and denominator bit lengths at most $B_C(1+\lceil\log_2 n\rceil)$.
--
--   The oracle may use exact real answers to choose subsequent queries. This result supplies a lower bound against the full adaptive model, with natural logarithm inside the denominator of the radical.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: O, Ω and Θ query bounds with stated constant dependencies → positive existential constants and integer thresholds before every order and proximity, with ENNReal infima of feasible natural caps; reason: the discrete feasible caps have an attained least value when nonempty; the empty infimum is infinity
--   - encoding: hard inputs with O_C(log n)-bit rational entries (absolute in Theorem 6.12) → the lower bound also holds for the rational input promise with a uniform numerator and denominator bit bound; reason: the source hard distributions use only these finite alphabets; no upper-bound or general input restriction is added
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 31, Theorem 6.11 (PDF p. 32); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_testing

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem adaptive_bounded_range_lower_bound :
    ∀ C : ℝ, ∀ hC : 2 < C, ∃ c : ℝ, ∃ N B : ℕ, 0 < c ∧ 3 ≤ N ∧ 0 < B ∧
      ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1/80 →
        ∀ (repairs oneSided : Bool),
          ENNReal.ofReal (c * adaptiveRate n) ≤
            Q (boundedProblem C (by linarith) repairs) n oneSided false ε ∧
          ENNReal.ofReal (c * adaptiveRate n) ≤
            rationalQ (boundedProblem C (by linarith) repairs) B n oneSided false ε := by sorry

end MetricTesting.Characterization.Supplement
