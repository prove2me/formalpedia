-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_theorem_1_4
-- name    : KSATSingleFlip.Connect.theorem_1_4
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:09:10.349093+00:00
-- url     : https://prove2.me/theorems/c29c6acc-ca85-42a3-99ce-0d69e18c6064
-- title:
--   Theorem 1.4 — Shattering with linear energy barriers
-- statement:
--   For all sufficiently large $k$ there are positive rates $a_k,b_k,c_k$ such that, for all sufficiently large $n$ and every integer $m$ with density $\alpha=m/n$ in the interval
--
--   $$\frac{2^k}{k}\bigl(\ln k+\ln\ln k+\ln(34/13)\bigr)\le\alpha\le2^k\bigl(\ln 2-1/\ln k\bigr),$$
--
--   a random $k$-SAT formula is satisfiable with probability at least $1-1/n$ and its solutions partition into regions of mass at most $e^{-a_kn}$, pairwise Hamming distance at least $b_kn$, and a barrier of at least $c_kn$ violated clause occurrences along every Boolean single-variable-flip path between distinct regions. The rates depend on $k$ and are uniform in $n$ and throughout the displayed density interval.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, Theorem 1.4, printed p. 4 (PDF p. 6), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Shattering

namespace KSATSingleFlip.Connect

/-- Theorem 1.4 of Wang, Yin, Yu and Zhang: uniformly throughout the stated
range, with high probability the solution set shatters with linear barriers. -/
theorem theorem_1_4 :
    ∃ k0 : ℕ, ∀ k ≥ k0,
      ∃ massRate separationRate energyRate : ℝ,
        0 < massRate ∧ 0 < separationRate ∧ 0 < energyRate ∧
        ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℕ,
          shatteringDensityLower k ≤ (m : ℝ) / n →
          (m : ℝ) / n ≤ shatteringDensityUpper k →
          1 - 1 / (n : ℝ) ≤ formulaProb n k m (fun F =>
            ∃ regions, IsShattered (ofFormula F) massRate separationRate energyRate regions) := by
  sorry

end KSATSingleFlip.Connect
