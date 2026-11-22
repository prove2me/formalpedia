-- Prove2me | Theorems.Thm_GRH_least_prime_modEq_of_thetaAP_square_root_log
-- name    : GRH.least_prime_modEq_of_thetaAP_square_root_log
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-21T21:29:20.174577+00:00
-- url     : https://prove2.me/theorems/dd3d67ce-ed00-432d-aecf-bbd57ac34c0d
-- title:
--   Chowla's least prime $\le K q^2\log^2 q$ from a one-logarithm Chebyshev bound
-- statement:
--   Derive **Chowla's 1934 conditional bound on the least prime in an arithmetic progression** from a uniform one-logarithm Chebyshev lower bound.
--
--   Input: an absolute constant $C\ge0$ with
--   $$\theta(x;q,a)\;\ge\;\frac{x}{\varphi(q)}-C\sqrt{x}\log x$$
--   for all moduli $q\ge1$, all $a$ coprime to $q$, and all real $x\ge2$ (child `GRH.grh_implies_thetaAP_square_root_log`).
--
--   Output: an absolute constant $K\ge0$ such that for every $q\ge2$ and every $a$ with $\gcd(a,q)=1$ some prime $p\le K q^2(\log q)^2$ satisfies $p\equiv a\pmod q$.
--
--   The proof balances at $x=K q^2(\log q)^2$: the main term $x/\varphi(q)\ge K q(\log q)^2$ dominates the error $C\sqrt{x}\log x$ once $\sqrt K$ exceeds a fixed multiple of $C$ (the sum is over primes only, so no prime-power noise enters); the prime sum then exceeds zero and produces the required prime. The concrete choice $K=(64(C+1)(C+2)^2)^2$ verifies uniformly for all $q\ge2$ and all $C\ge0$.
-- source:
--   https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis (section 'Consequences of GRH': 'In 1934, Chowla showed that the generalized Riemann hypothesis implies that the first prime in the arithmetic progression a mod m is at most K m² log(m)² for some fixed constant K'; oldid 1378052002). Original: S. Chowla, 'On the least prime in an arithmetical progression', J. Indian Math. Soc. (N.S.) 1 (1934). Step 2 (bridge) of the reduction of GRH.grh_implies_least_prime_modEq.

import Mathlib

namespace GRH

/-- **Chowla's least-prime bound from a sharp Chebyshev lower bound (bridge).**
Given an absolute constant C ≥ 0 with the uniform one-logarithm Chebyshev lower bound

    θ(x; q, a) ≥ x / φ(q) - C * sqrt x * log x

for all moduli q ≥ 1, all a coprime to q, and all real x ≥ 2, there is an absolute constant
K ≥ 0 such that for every q ≥ 2 and every a coprime to q some prime p ≤ K * q^2 * (log q)^2
satisfies p ≡ a [MOD q].

The proof balances at x = K * q^2 * (log q)^2: the main term x / φ(q) ≥ K * q * (log q)^2
dominates the error C * sqrt x * log x once sqrt K exceeds a fixed multiple of C, so the prime
sum exceeds zero and yields the desired prime; the sum is over primes only, so no prime-power
noise enters. The concrete choice K = (64 * (C + 1) * (C + 2)^2)^2 makes the logarithmic
arithmetic work uniformly for q ≥ 2. -/
theorem least_prime_modEq_of_thetaAP_square_root_log
    (C : ℝ) (hC : 0 ≤ C)
    (hθ : ∀ (q a : ℕ), q ≠ 0 → a.Coprime q → ∀ x : ℝ, 2 ≤ x →
        x / (q.totient : ℝ) - C * Real.sqrt x * Real.log x ≤
          ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q] ∧ n.Prime),
            Real.log (n : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (q : ℕ), 2 ≤ q → ∀ (a : ℕ), a.Coprime q →
        ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧
          (p : ℝ) ≤ K * (q : ℝ) ^ 2 * (Real.log q) ^ 2 := by sorry

end GRH
