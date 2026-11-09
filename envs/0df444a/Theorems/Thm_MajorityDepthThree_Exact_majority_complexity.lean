-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_majority_complexity
-- name    : MajorityDepthThree.Exact.majority_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:44.705028+00:00
-- url     : https://prove2.me/theorems/a4b1a5b0-15a4-44b8-8fd0-98f481e4d781
-- title:
--   Corollary 1.5 — exact majority complexity (corrected: odd-n finite bound)
-- statement:
--   For $n\in\mathbb N$, let $u=\lceil n/2\rceil$ and let $s(n),s^+(n)$ be the minimum top fan-ins of signed and monotone width-three OR-AND-OR circuits computing $|S|\ge u$ on every Boolean input. Put $a=2/6^{1/4}$. Both minima are positive and attained by actual circuits, and for every $n$,
--
--   $$\frac{\binom n{\lfloor n/2\rfloor}}{2^u(3/2)^{(n-u)/2}}\le s(n)\le s^+(n).$$
--
--   There exist absolute $C>0$ and $d\in\mathbb N$, chosen before $n$, such that
--
--   $$s^+(n)\le C(n+1)^d a^n\quad\text{for every }n.$$
--
--   Both models retain the precise exponential conclusion:
--
--   $$\lim_{n\to\infty}\frac{\log s(n)}n=\log a=\lim_{n\to\infty}\frac{\log s^+(n)}n.$$
--
--   At $n=0$ both minima equal one. The displayed denominator equals $6^{n/4}$ for even $n$ and $(8/3)^{1/4}6^{n/4}$ for odd $n$. This is the minimal parity correction derived from Theorem 1.4 at $t=u$, with the numerator unchanged by binomial symmetry. The result determines both models up to polynomial factors, retaining the abstract's precision as well as the two asymptotic displays.
--
--   Differences from the source:
--   - correction: For all n the lower denominator is 6^(n/4) → For u=ceil(n/2), the denominator is 2^u(3/2)^((n-u)/2), inserting (8/3)^(1/4) only when n is odd; reason: At n=5 the CNF of all ten positive triples computes conventional majority with top fan-in one, while the printed lower bound 10/6^(5/4)>1 since 10000>7776; Theorem 1.4 at u supplies this correction
--   - encoding: n Boolean variables → The fixed carrier Fin n with ambient set univ; reason: Relabeling preserves clauses, assignments, weights and top fan-in; the theorem retains its stated parameter domain
--   - encoding: Both complexities equal a^(n+o(n)), with polynomial-factor precision in the abstract → Both logarithmic rates tend to log(a), with a uniform polynomial upper bound and the explicit finite lower bound; reason: Since a>1 and both minima are positive, the limits are equivalent to the two o(n) exponent statements; the polynomial bound retains the stronger abstract claim
--   - encoding: Minimum circuit sizes, with no explicit convention for zero variables → Actual witness circuits realizing both minima, positivity, and sizes one at n=0; reason: These expose the semantics of minimum and constant true majority; no witness or size bound is assumed
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.4, Corollary 1.5; p.1, abstract (polynomial-factor precision); p.4, Theorem 1.4 (finite correction)

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem majority_complexity  :
    (∀ n : ℕ,
      (Nat.choose n (n / 2) : ℝ) / countingBound n (majorityThreshold n) ≤ (majoritySize n : ℝ) ∧
      majoritySize n ≤ monotoneMajoritySize n ∧
      0 < majoritySize n ∧
      (∃ C : Circuit (Fin n), CircuitValid Finset.univ 3 C ∧
        ComputesThreshold Finset.univ (majorityThreshold n) C ∧ C.length = majoritySize n) ∧
      (∃ C : Circuit (Fin n), CircuitValid Finset.univ 3 C ∧ CircuitMonotone C ∧
        ComputesThreshold Finset.univ (majorityThreshold n) C ∧ C.length = monotoneMajoritySize n)) ∧
    (∃ constant : ℝ, 0 < constant ∧ ∃ degree : ℕ, ∀ n : ℕ,
      (monotoneMajoritySize n : ℝ) ≤ constant * ((n : ℝ) + 1)^degree * exponentialBase^n) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (majoritySize n : ℝ) / (n : ℝ))
      Filter.atTop (nhds (Real.log exponentialBase)) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (monotoneMajoritySize n : ℝ) / (n : ℝ))
      Filter.atTop (nhds (Real.log exponentialBase)) ∧
    majoritySize 0 = 1 ∧ monotoneMajoritySize 0 = 1 := by sorry

end MajorityDepthThree.Exact
