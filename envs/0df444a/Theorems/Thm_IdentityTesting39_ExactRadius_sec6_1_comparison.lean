-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_sec6_1_comparison
-- name    : IdentityTesting39.ExactRadius.sec6_1_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:51.771287+00:00
-- url     : https://prove2.me/theorems/8436b76b-26b5-477a-8a7a-0686228d9562
-- title:
--   §6.1 — small-objective deficit-to-excess comparison
-- statement:
--   There are absolute $j_0,K>0$ for the fixed head threshold $h_*=1/8$. Let $q$ be a finite probability reference with a largest label $i_0$ of mass $h\in[1/8,1)$ and tail mass $\alpha=1-h$. At a nonempty strict radius $\varepsilon$, suppose the deficit branch is feasible and $n\alpha\ge1$. Then
--
--   $$J_n^-(q,\varepsilon)\le j_0\quad\Longrightarrow\quad J_n^+(q,\varepsilon)\le KJ_n^-(q,\varepsilon).$$
--
--   The radius is unchanged, and the constants are uniform over the reference and the label count. This is the small-objective branch comparison used in the large-atom upper bound.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - encoding: universal O or Ω comparison constants → positive existential constants precede all instance data and label types; reason: this is the universal meaning of the source asymptotics
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.8, §6.1, small-objective comparison; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_MomentPrograms

namespace IdentityTesting39.ExactRadius

/-- §6.1, printed p.8 / PDF p.9, with h_* fixed to 1/8. -/
theorem sec6_1_comparison :
    ∃ j₀ K : ℝ, 0 < j₀ ∧ 0 < K ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε n : ℝ) (i₀ : ι),
      ProbabilityVector q → StrictRadius q ε → Largest q i₀ →
      1/8 ≤ q i₀ → q i₀ < 1 → 1 ≤ n*(1-q i₀) →
      (feasibleMoments q ε (.deficit i₀)).Nonempty →
      programValue q ε n (.deficit i₀) ≤ j₀ →
      programValue q ε n (.excess i₀) ≤ K*programValue q ε n (.deficit i₀) := by sorry

end IdentityTesting39.ExactRadius
