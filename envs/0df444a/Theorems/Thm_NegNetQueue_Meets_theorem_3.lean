-- Prove2me | Theorems.Thm_NegNetQueue_Meets_theorem_3
-- name    : NegNetQueue.Meets.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:23.350027+00:00
-- url     : https://prove2.me/theorems/59c81033-f872-4c18-a289-f75176725f8d
-- title:
--   Theorem 3, p. 10 — joint law (3) of X_j and Y_j in the M/M/c/n queue, X_n ∼ X_{n−1}, and the corollaries (4), (5)
-- statement:
--   Let $\varepsilon$ be an event sequence of an M/M/c/n queue with $n\ge2$ and server utilization factor $\rho=\lambda/(c\mu)$. For a customer arriving at position $j\in\{1,\dots,n-1\}$, let $X_j$ be the number of later arrivals she meets before entering service and $Y_j$ the number among them who fill up the queue (arrive to position $n$). Write $B_0(x)=\binom{j+x-1}{j-1}-\binom{j+x-1}{n-1}$ and $B_1(d)=\binom{j+d-1}{n-2}-\binom{j+d-1}{n-1}$. Then:
--   1. **(3)** for all $x,y\ge 0$, with $d=x-y$,
--   $$P(X_j=x,Y_j=y)=\begin{cases}B_0(x)\,\dfrac{\rho^x}{(1+\rho)^{j+x}} & 0=y\le x<n,\\[2mm] B_1(d)\,\dfrac{\rho^x}{(1+\rho)^{j+d}} & 0<y\le x<n,\\[2mm] 0 & \text{otherwise;}\end{cases}$$
--   2. $X_n$ has the same distribution as $X_{n-1}$;
--   3. **(4)** for every function $\psi$ on the nonnegative integers,
--   $$E[\psi(X_j)]=\Big(\frac{1}{1+\rho}\Big)^j\left[\sum_{x=0}^{n-1}B_0(x)\Big(\frac{\rho}{1+\rho}\Big)^x\psi(x)+\sum_{d=0}^{n-2}B_1(d)\Big(\frac{1}{1+\rho}\Big)^d\sum_{x=d+1}^{n-1}\rho^x\psi(x)\right];$$
--   4. **(5)** for every real $s$ with $s\rho\ne1$, the generating function $G_j(s)=E[s^{X_j}]$ is
--   $$G_j(s)=\Big(\frac{1}{1+\rho}\Big)^j\left[\sum_{x=0}^{n-1}B_0(x)\Big(\frac{\rho s}{1+\rho}\Big)^x+\sum_{d=0}^{n-2}B_1(d)\Big(\frac{1}{1+\rho}\Big)^d\frac{(s\rho)^n-(s\rho)^{d+1}}{s\rho-1}\right].$$
--
--   Theorem 3 gives the exposure of a joining customer in closed form; through (5) it yields the expected utility $U_j=R-S(1-\eta^{j-1}G_j(\eta))$ of the exponential loss model (6).
--
--   **Formalization Note.** The M/M/c/n queue during the wait is represented by its i.i.d. event sequence (see the definition `EventSeq`), for every $\lambda,\mu>0$, $c\ge1$ and every probability space carrying such a sequence. $n\ge2$ is required by the page. (3) is read as including probability $0$ off its two ranges. Binomial coefficients are cast to real numbers before subtracting. $X_j$ is at most $n$ everywhere, so its conversion to a natural number in (4) and (5) is exact, and $\psi(X_j)$, $s^{X_j}$ take finitely many values, so no integrability hypothesis is needed.
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), p. 10, Theorem 3, displays (3), (4), (5)

import Mathlib
import Definitions.Def_NegNetQueue_Meets_EventSeq
import Definitions.Def_NegNetQueue_Meets_Model

namespace NegNetQueue.Meets

open MeasureTheory ProbabilityTheory

/-- Theorem 3, p. 10, in full: (3) with its support, `X_n ∼ X_{n-1}`, the expectation formula (4) for
every `ψ`, and the generating function (5) for `sρ ≠ 1`. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam mu : ℝ) (c : ℕ)
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
    (∀ x : ℕ∞, P {ω | Xmet n n ε ω = x} = P {ω | Xmet n (n - 1) ε ω = x}) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ∀ ψ : ℕ → ℝ,
      ∫ ω, ψ (Xmet n j ε ω).toNat ∂P =
        (1 / (1 + rho lam mu c)) ^ j *
          (∑ x ∈ Finset.range n,
              ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
                (rho lam mu c / (1 + rho lam mu c)) ^ x * ψ x +
            ∑ d ∈ Finset.range (n - 1),
              ((Nat.choose (j + d - 1) (n - 2) : ℝ) - (Nat.choose (j + d - 1) (n - 1) : ℝ)) *
                (1 / (1 + rho lam mu c)) ^ d *
                ∑ x ∈ Finset.Ico (d + 1) n, rho lam mu c ^ x * ψ x)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ∀ s : ℝ, s * rho lam mu c ≠ 1 →
      ∫ ω, s ^ (Xmet n j ε ω).toNat ∂P =
        (1 / (1 + rho lam mu c)) ^ j *
          (∑ x ∈ Finset.range n,
              ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
                (rho lam mu c * s / (1 + rho lam mu c)) ^ x +
            ∑ d ∈ Finset.range (n - 1),
              ((Nat.choose (j + d - 1) (n - 2) : ℝ) - (Nat.choose (j + d - 1) (n - 1) : ℝ)) *
                (1 / (1 + rho lam mu c)) ^ d *
                (((s * rho lam mu c) ^ n - (s * rho lam mu c) ^ (d + 1)) /
                  (s * rho lam mu c - 1)))) := by sorry

end NegNetQueue.Meets
