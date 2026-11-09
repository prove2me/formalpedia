-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_eq_4_baseline
-- name    : IdentityTesting39.ExactRadius.eq_4_baseline
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:59.280584+00:00
-- url     : https://prove2.me/theorems/bbb0de56-f339-4c9d-abe0-5bbcb0e99f8f
-- title:
--   §3, (4) — universal inverse-radius baseline
-- statement:
--   There are absolute positive constants $c,C$ such that for every finite probability reference $q$ and nonempty strict radius $\varepsilon$, every admissible fixed sample count $m$ satisfies
--
--   $$c/\varepsilon\le m.$$
--
--   If $q$ is a point mass, an admissible count exists and
--
--   $$N^*(q,\varepsilon)\le C/\varepsilon.$$
--
--   Thus the baseline is uniform over all reference vectors and domain sizes, and is sharp for point masses. Quantifying the lower bound over admissible counts avoids assuming the finiteness of $N^*$ before it is proved.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - reading: least fixed sample size permitting the two error bounds in §2 → tests are rejection-probability functions with values in [0,1]; reason: Appendix A explicitly uses randomized testers and §4 uses internal Poisson-simulation randomness
--   - encoding: universal O or Ω comparison constants → positive existential constants precede all instance data and label types; reason: this is the universal meaning of the source asymptotics
--   - encoding: N* = Ω(1/ε) → every admissible m satisfies c/ε≤m; reason: equivalent once admissible counts exist; nonemptiness is separately proved for point masses and in the goal
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.4, §3, display (4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_StatisticalModel

namespace IdentityTesting39.ExactRadius

/-- §3, (4), printed p.4 / PDF p.5. Constants are uniform even over the label type. -/
theorem eq_4_baseline :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (ι : Type) [Fintype ι] (q : ι → ℝ) (ε : ℝ),
      ProbabilityVector q → StrictRadius q ε →
      (∀ m ∈ admissibleSizes q ε, c/ε ≤ (m : ℝ)) ∧
      ((∃ i₀, q i₀ = 1) → (admissibleSizes q ε).Nonempty ∧
        (sampleComplexity q ε : ℝ) ≤ C/ε) := by sorry

end IdentityTesting39.ExactRadius
