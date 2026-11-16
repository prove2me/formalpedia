-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_sharp_nonadaptive_complexity
-- name    : MetricTesting.Characterization.Supplement.sharp_nonadaptive_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:27:40.419709+00:00
-- url     : https://prove2.me/theorems/79e1690b-c547-4694-9d2f-7c03c9afd0fd
-- title:
--   Theorem 6.8 — Sharp nonadaptive bounded-range complexity
-- statement:
--   For every fixed real $C>1$, there is $A_C>0$ such that for all $n\ge3$ and $0<\epsilon\le1$, the one-sided nonadaptive complexity obeys
--
--   $$Q_{\rm na}^{(1)}(n,\epsilon;C)\le A_CF(n,\epsilon),$$
--
--   and is zero if $C\le2$. There is an absolute $c>0$ such that for every $C>2$ there are $A_C>0$, $N_C\ge3$ and a positive bit constant $B_C$ with, for all $n\ge N_C$ and $0<\epsilon\le1/80$,
--
--   $$cF(n,\epsilon)\le Q_{\rm na}^{(2)}(n,\epsilon;C)\le Q_{\rm na}^{(1)}(n,\epsilon;C)\le A_CF(n,\epsilon).$$
--
--   The lower bound also holds when the success guarantee is required only on inputs whose reduced rational entries have at most $B_C(1+\lceil\log_2 n\rceil)$ numerator and denominator bits. All these assertions hold for bounded repairs and for arbitrary positive metric repairs.
--
--   The rate $F$ includes all four proximity regimes. Upper bounds apply to every real input in the ambient range; the rational-promise lower bound expresses that the hard inputs have logarithmic bit size, using the same operational tester model.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: O, Ω and Θ query bounds with stated constant dependencies → positive existential constants and integer thresholds before every order and proximity, with ENNReal infima of feasible natural caps; reason: the discrete feasible caps have an attained least value when nonempty; the empty infimum is infinity
--   - encoding: hard inputs with O_C(log n)-bit rational entries (absolute in Theorem 6.12) → the lower bound also holds for the rational input promise with a uniform numerator and denominator bit bound; reason: the source hard distributions use only these finite alphabets; no upper-bound or general input restriction is added
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 29, Theorem 6.8 (PDF p. 30); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_testing

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem sharp_nonadaptive_complexity :
    (∀ C : ℝ, ∀ hC : 1 < C, ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, 3 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ repairs : Bool,
        Q (boundedProblem C hC repairs) n true true ε ≤ ENNReal.ofReal (A * rate n ε) ∧
        (C ≤ 2 → Q (boundedProblem C hC repairs) n true true ε = 0)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ C : ℝ, ∀ hC : 2 < C,
      ∃ A : ℝ, ∃ N B : ℕ, 0 < A ∧ 3 ≤ N ∧ 0 < B ∧
        ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1/80 → ∀ repairs : Bool,
          ENNReal.ofReal (c * rate n ε) ≤ Q (boundedProblem C (by linarith) repairs) n false true ε ∧
          Q (boundedProblem C (by linarith) repairs) n false true ε ≤
            Q (boundedProblem C (by linarith) repairs) n true true ε ∧
          Q (boundedProblem C (by linarith) repairs) n true true ε ≤ ENNReal.ofReal (A * rate n ε) ∧
          ENNReal.ofReal (c * rate n ε) ≤
            rationalQ (boundedProblem C (by linarith) repairs) B n false true ε) := by sorry

end MetricTesting.Characterization.Supplement
