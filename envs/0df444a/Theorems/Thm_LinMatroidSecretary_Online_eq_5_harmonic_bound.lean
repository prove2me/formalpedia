-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_eq_5_harmonic_bound
-- name    : LinMatroidSecretary.Online.eq_5_harmonic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:09.40046+00:00
-- url     : https://prove2.me/theorems/dbd2f558-7700-4697-923d-863712685f13
-- title:
--   §2.3 (5) — the cutoff k = ⌊n/e⌋ gives (k/n) Σ_{j=k}^{n−1} 1/j ≥ 1/e
-- statement:
--   Let $n\ge3$ and $k=\lfloor n/e\rfloor$. Then
--   1. $\displaystyle\frac1n\sum_{i=k+1}^{n}\frac{k}{i-1}=\frac kn\sum_{j=k}^{n-1}\frac1j$;
--   2. $\displaystyle k\sum_{j=k}^{n-1}\frac1j=1+k\sum_{j=k+1}^{n-1}\frac1j$;
--   3. $\displaystyle 1+k\sum_{j=k+1}^{n-1}\frac1j\ \ge\ 1+k\int_{k+1}^{n}\frac{dx}x$;
--   4. $\displaystyle\int_{k+1}^{n}\frac{dx}x=\ln\frac{n}{k+1}$;
--   5. $\displaystyle 1+k\ln\frac{n}{k+1}\ \ge\ \frac ne$;
--   6. consequently $\displaystyle\frac kn\sum_{j=k}^{n-1}\frac1j\ \ge\ \frac1e$.
--
--   In addition, for every finite field $F$, every dimension $d$, every finite value-ordered ground type $R$ with $|R|=n$, every vector family $v:R\to F^d$ and every $e\in\mathrm{OPT}(R)$, Algorithm 1 with sample size $k$ satisfies both probability equalities in (5):
--   $$\Pr[e\in\mathrm{ALG}]=\frac1n\sum_{i=k+1}^{n}\frac{k}{i-1}=\frac kn\sum_{j=k}^{n-1}\frac1j.$$
--   Thus the statement includes the actual selection probability as well as the cutoff arithmetic.
--
--   Differences from the source:
--   - encoding: k = ⌊n/e⌋, 1/e, ln → Nat.floor (n / Real.exp 1), 1 / Real.exp 1, Real.log; reason: standard Lean functions; n/(k+1) > 0 and k ≥ 1 for n ≥ 3, so no junk value is reached
--   - encoding: Algorithm 1 selection probability under uniformly random arrivals and its internal randomness → selProb (alg1 k), using exact finite sums over bijections and decision vectors and the rank-sorted fixed-choice table; reason: these definitions implement Algorithms 1–2 with fresh acceptance randomness and the uniform order; both probability equalities of (5) are included
--   - encoding: weights with a fixed tie-breaking order → a LinearOrder on the ground type, with larger elements ranked better; reason: every weighted instance induces this value order, and the ordinal algorithm and OPT depend only on it
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), §2.3, display (5) and the estimate that follows it, PDF p. 12 (printed p. 10)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Algorithm

namespace LinMatroidSecretary.Online

/-- §2.3, (5) and the estimate after it (PDF p. 12, printed 10): for `n ≥ 3` and `k = ⌊n/e⌋`,
`(1/n) ∑_{i=k+1}^{n} k/(i−1) = (k/n) ∑_{j=k}^{n−1} 1/j`,
`k ∑_{j=k}^{n−1} 1/j = 1 + k ∑_{j=k+1}^{n−1} 1/j ≥ 1 + k ∫_{k+1}^{n} dx/x = 1 + k ln(n/(k+1))`,
`1 + k ln(n/(k+1)) ≥ n/e`, and hence `(k/n) ∑_{j=k}^{n−1} 1/j ≥ 1/e`.
For Algorithm 1 on every finite-field instance and every `e ∈ OPT(E)`, (5) also identifies
the actual selection probability with both displayed sums. -/
theorem eq_5_harmonic_bound (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : k = ⌊(n : ℝ) / Real.exp 1⌋₊) :
    (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc (k + 1) n, (k : ℝ) / ((i : ℝ) - 1) =
        ((k : ℝ) / (n : ℝ)) * ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ) ∧
      (k : ℝ) * ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ) =
        1 + (k : ℝ) * ∑ j ∈ Finset.Ico (k + 1) n, 1 / (j : ℝ) ∧
      1 + (k : ℝ) * (∫ x in ((k : ℝ) + 1)..(n : ℝ), x⁻¹) ≤
        1 + (k : ℝ) * ∑ j ∈ Finset.Ico (k + 1) n, 1 / (j : ℝ) ∧
      (∫ x in ((k : ℝ) + 1)..(n : ℝ), x⁻¹) = Real.log ((n : ℝ) / ((k : ℝ) + 1)) ∧
      (n : ℝ) / Real.exp 1 ≤ 1 + (k : ℝ) * Real.log ((n : ℝ) / ((k : ℝ) + 1)) ∧
      1 / Real.exp 1 ≤ ((k : ℝ) / (n : ℝ)) * ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ) ∧
      (∀ (F : Type*) [Field F] [Fintype F] (d : ℕ) (R : Type*) [Fintype R] [LinearOrder R],
        Fintype.card R = n → ∀ (v : R → Fin d → F) (e : R), e ∈ OPT F v Finset.univ →
          selProb (alg1 (n := n) k) v e =
            (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc (k + 1) n, (k : ℝ) / ((i : ℝ) - 1) ∧
          selProb (alg1 (n := n) k) v e =
            ((k : ℝ) / (n : ℝ)) * ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ)) := by sorry

end LinMatroidSecretary.Online
