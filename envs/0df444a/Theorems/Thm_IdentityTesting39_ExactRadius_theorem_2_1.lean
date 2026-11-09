-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_theorem_2_1
-- name    : IdentityTesting39.ExactRadius.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:23.194827+00:00
-- url     : https://prove2.me/theorems/582ebd1c-3eb1-4f85-b8ab-e3ab740fa214
-- title:
--   Theorem 2.1 — exact-radius sample complexity and explicit linear-size SOC programs
-- statement:
--   There exist universal positive constants $c,C,K$. Let $q$ be any probability vector on a finite label set of size $k$, let $\varepsilon>0$ have a nonempty strict alternative, and let $i_0$ be any largest label. The set of admissible fixed sample counts is nonempty, and off the point mass the real root set is nonempty. Then
--
--   $$cR(q,\varepsilon,i_0)\le N^*(q,\varepsilon)\le CR(q,\varepsilon,i_0).$$
--
--   Here $N^*$ is defined statistically by randomized tests with each error at most $1/3$, while $R$ is defined independently from the scalar moment programs with the baseline $1/\varepsilon$. Every constraint uses the identical input radius $\varepsilon$.
--
--   For every real $n>0$, the applicable explicit second-order-cone instances have at most $Kk$ real variables, at most $Kk$ constraints and total cone dimension at most $Kk$. Each has an attained minimum equal to its moment-program value. This applies to the all-coordinate program when $q_{i_0}<1/8$, to the head-deleted excess program when $q_{i_0}\in[1/8,1)$, and to the deficit companion there when $\varepsilon\le1-q_{i_0}$. The point-mass root is directly $1/\varepsilon$. All three constants are independent of $q,\varepsilon,k$ and the largest-label choice.
--
--   The result identifies finite-domain identity-testing sample complexity with a finite convex optimization functional at the exact requested radius, including the explicit program-size clause.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - reading: least fixed sample size permitting the two error bounds in §2 → tests are rejection-probability functions with values in [0,1]; reason: Appendix A explicitly uses randomized testers and §4 uses internal Poisson-simulation randomness
--   - reading: relabel a largest atom → the root and its bounds are quantified over every largest label; reason: no tie-breaking rule is specified; every choice is retained
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - encoding: universal O or Ω comparison constants → positive existential constants precede all instance data and label types; reason: this is the universal meaning of the source asymptotics
--   - encoding: O(k) variables and constraints with explicit second-order-cone representations → the defined affine SOC instances have linear variable, constraint and total cone-dimension bounds and attained equality of minima; reason: an explicit coefficient construction and dimension bound exclude encoding F_n itself in a coefficient or hiding size in a single large cone
--   - encoding: least sample size and real sample root → nonemptiness of admissible counts and of the off-point-mass root set are explicit conjuncts; reason: these assert existence rather than assuming it or relying on empty infima
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.3, Theorem 2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_SecondOrderCone

namespace IdentityTesting39.ExactRadius

/-- Theorem 2.1, printed p.3 / PDF p.4, including the size and explicit SOC clause. -/
theorem theorem_2_1 :
    ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 < K ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε : ℝ) (i₀ : ι),
      ProbabilityVector q → StrictRadius q ε → Largest q i₀ →
      (admissibleSizes q ε).Nonempty ∧
      (q i₀ < 1 → (rootSet q ε i₀).Nonempty) ∧
      c*sampleRoot q ε i₀ ≤ (sampleComplexity q ε : ℝ) ∧
      (sampleComplexity q ε : ℝ) ≤ C*sampleRoot q ε i₀ ∧
      ∀ n : ℝ, 0 < n → ∀ B : Branch ι, Applicable q ε i₀ B → SOCClaim K q ε n B := by sorry

end IdentityTesting39.ExactRadius
