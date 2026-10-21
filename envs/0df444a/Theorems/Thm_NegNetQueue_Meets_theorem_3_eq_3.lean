-- Prove2me | Theorems.Thm_NegNetQueue_Meets_theorem_3_eq_3
-- name    : NegNetQueue.Meets.theorem_3_eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:18.144228+00:00
-- url     : https://prove2.me/theorems/90e0ce77-cf09-41ce-bd3b-6298d94ba558
-- title:
--   Theorem 3, (3), p. 10 — the joint law of (X_j, Y_j), and X_n ∼ X_{n−1}
-- statement:
--   Let $\varepsilon$ be an event sequence of an M/M/c/n queue with $n\ge 2$ and server utilization factor $\rho=\lambda/(c\mu)$. For a customer arriving at position $j\in\{1,\dots,n-1\}$, let $X_j$ be the number of later arrivals she meets before entering service and $Y_j$ the number among them who fill up the queue (arrive to position $n$). With $d=x-y$, for all integers $x,y\ge0$:
--   $$P(X_j=x,Y_j=0)=\left[\binom{j+x-1}{j-1}-\binom{j+x-1}{n-1}\right]\frac{\rho^x}{(1+\rho)^{j+x}},\qquad 0=y\le x<n,$$
--   $$P(X_j=x,Y_j=y)=\left[\binom{j+d-1}{n-2}-\binom{j+d-1}{n-1}\right]\frac{\rho^x}{(1+\rho)^{j+d}},\qquad 0<y\le x<n,$$
--   and $P(X_j=x,Y_j=y)=0$ for every other pair $(x,y)$. Moreover $X_n$ has the same distribution as $X_{n-1}$.
--
--   This is the closed-form joint law (3), the core of Theorem 3; the corollaries (4) and (5) follow from it by summation.
--
--   **Formalization Note.** "Have the following joint distribution" is read as including probability $0$ off the two ranges. Binomial coefficients are cast to real numbers before subtracting. $n\ge2$ is required by the page ($j\in\{1,\dots,n-1\}$ and the coefficient $\binom{\cdot}{n-2}$). The distributions of $X_n$ and $X_{n-1}$ are compared on every value in $\mathbb N\cup\{\infty\}$.
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), p. 10, Theorem 3, display (3) and the sentence 'The distribution of Xn is the same as that of Xn−1'

import Mathlib
import Definitions.Def_NegNetQueue_Meets_EventSeq
import Definitions.Def_NegNetQueue_Meets_Model

namespace NegNetQueue.Meets

open MeasureTheory ProbabilityTheory

/-- Theorem 3, (3), p. 10: the joint law of `(X_j, Y_j)` for `j ∈ {1, …, n-1}` (probability `0` off
the two ranges of (3)), and `X_n` has the same law as `X_{n-1}`. -/
theorem theorem_3_eq_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam mu : ℝ) (c : ℕ)
    (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c) (ε : ℕ → Ω → Bool)
    (hε : IsEventSeq P lam mu c ε) (n : ℕ) (hn : 2 ≤ n) :
    (∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ∀ x y : ℕ,
      (P {ω | Xmet n j ε ω = (x : ℕ∞) ∧ Yfill n j ε ω = (y : ℕ∞)}).toReal =
        if y = 0 ∧ x < n then
          ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
            rho lam mu c ^ x / (1 + rho lam mu c) ^ (j + x)
        else if 0 < y ∧ y ≤ x ∧ x < n then
          ((Nat.choose (j + (x - y) - 1) (n - 2) : ℝ) - (Nat.choose (j + (x - y) - 1) (n - 1) : ℝ)) *
            rho lam mu c ^ x / (1 + rho lam mu c) ^ (j + (x - y))
        else 0) ∧
    (∀ x : ℕ∞, P {ω | Xmet n n ε ω = x} = P {ω | Xmet n (n - 1) ε ω = x}) := by sorry

end NegNetQueue.Meets
