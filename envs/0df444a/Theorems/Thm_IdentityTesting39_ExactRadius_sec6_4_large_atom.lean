-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_sec6_4_large_atom
-- name    : IdentityTesting39.ExactRadius.sec6_4_large_atom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:08.615305+00:00
-- url     : https://prove2.me/theorems/cef75697-a690-4aef-98e9-05b8cfa57a19
-- title:
--   §6.4 — sample-root characterization for a large reference atom
-- statement:
--   There are absolute $c,C>0$ such that for every finite probability vector $q$, every largest label $i_0$ of mass in $[1/8,1)$, and every nonempty strict radius $\varepsilon$,
--
--   $$cR(q,\varepsilon,i_0)\le m\quad\text{for every admissible }m,\qquad N^*(q,\varepsilon)\le CR(q,\varepsilon,i_0).$$
--
--   An admissible sample count exists. The claim covers both $\varepsilon>2\alpha$ and $\varepsilon\le2\alpha$, where $\alpha=1-q_{i_0}$; it does not assume the radius is smaller than the tail mass. This completes the large-atom regime at the requested radius.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - reading: least fixed sample size permitting the two error bounds in §2 → tests are rejection-probability functions with values in [0,1]; reason: Appendix A explicitly uses randomized testers and §4 uses internal Poisson-simulation randomness
--   - reading: relabel a largest atom → the root and its bounds are quantified over every largest label; reason: no tie-breaking rule is specified; every choice is retained
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - encoding: universal O or Ω comparison constants → positive existential constants precede all instance data and label types; reason: this is the universal meaning of the source asymptotics
--   - encoding: the lower bound on N* → the inequality for every admissible m together with nonemptiness; reason: equivalent to the least-sample-count bound
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.9, §6.4, continuing on p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_MomentPrograms

namespace IdentityTesting39.ExactRadius

/-- §6.4, printed pp.9–10 / PDF pp.10–11: all nonempty strict radii. -/
theorem sec6_4_large_atom :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε : ℝ) (i₀ : ι),
      ProbabilityVector q → StrictRadius q ε → Largest q i₀ →
      1/8 ≤ q i₀ → q i₀ < 1 →
      (∀ m ∈ admissibleSizes q ε, c*sampleRoot q ε i₀ ≤ (m : ℝ)) ∧
      (admissibleSizes q ε).Nonempty ∧
      (sampleComplexity q ε : ℝ) ≤ C*sampleRoot q ε i₀ := by sorry

end IdentityTesting39.ExactRadius
