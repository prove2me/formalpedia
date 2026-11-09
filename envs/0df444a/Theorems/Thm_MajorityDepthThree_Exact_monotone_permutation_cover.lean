-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_monotone_permutation_cover
-- name    : MajorityDepthThree.Exact.monotone_permutation_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:31.355745+00:00
-- url     : https://prove2.me/theorems/c3c32ca3-c006-4789-94e4-053b5c32cdca
-- title:
--   Fact 2.10 — uniform permutation cover and general source paragraph
-- statement:
--   There exist absolute $C>0$ and $d\in\mathbb N$, chosen before $n,t,k$ and the formula, with the following property. For all $n,k\ge1$, $0\le t\le n$, and every valid monotone $t$-threshold $k$-CNF $F$ with $\theta_t(F)>0$, there is a monotone circuit $\mathcal C$ consisting of permutations of $F$, computing the threshold function on every input, such that
--
--   $$|\mathcal C|\le C(n+1)^d\frac{\binom nt}{\theta_t(F)}.$$
--
--   The item also states the extremal specialization in Fact 2.10, replacing the denominator by $\Theta(n,t,k)$ when $F$ is extremal. The same constants serve both clauses. The general clause is stated explicitly in the paragraph immediately before the numbered fact; it is needed for constructions that are not assumed extremal. The bound is polynomially precise and preserves the top fan-in metric.
--
--   Differences from the source:
--   - encoding: n Boolean variables → The fixed carrier Fin n with ambient set univ; reason: Relabeling preserves clauses, assignments, weights and top fan-in; the theorem retains its stated parameter domain
--   - generalization: Fact 2.10 assumes a monotone extremal formula → The preceding paragraph gives a cover for every monotone threshold formula with positive boundary count, followed by the extremal specialization; reason: The stronger assertion is stated explicitly in the same source paragraph and specializes by extremality
--   - encoding: poly(n) → A single existential C>0 and natural degree d before all n,t,k,F, using C(n+1)^d; reason: This is uniform polynomial slack; no numerical coefficient is invented
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.7, Fact 2.10 and immediately preceding paragraph

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem monotone_permutation_cover  :
    ∃ constant : ℝ, 0 < constant ∧ ∃ degree : ℕ,
    ∀ (n t k : ℕ), 1 ≤ n → 1 ≤ k → t ≤ n →
    (∀ F : CNF (Fin n), ValidCNF Finset.univ F → Width k F → Monotone F →
      Threshold Finset.univ F t → 0 < theta Finset.univ F t →
      ∃ C : Circuit (Fin n), CircuitValid Finset.univ k C ∧ CircuitMonotone C ∧
        ComputesThreshold Finset.univ t C ∧ PermutationsOf F C ∧
        (C.length : ℝ) ≤ constant * ((n : ℝ) + 1)^degree *
          (Nat.choose n t : ℝ) / (theta Finset.univ F t : ℝ)) ∧
    (∀ F : CNF (Fin n), Extremal Finset.univ F t k → Monotone F →
      ∃ C : Circuit (Fin n), CircuitValid Finset.univ k C ∧ CircuitMonotone C ∧
        ComputesThreshold Finset.univ t C ∧ PermutationsOf F C ∧
        (C.length : ℝ) ≤ constant * ((n : ℝ) + 1)^degree *
          (Nat.choose n t : ℝ) / (thetaMax (Finset.univ : Finset (Fin n)) t k : ℝ)) := by sorry

end MajorityDepthThree.Exact
