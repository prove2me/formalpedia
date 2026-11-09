-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_eq_3_scaling
-- name    : IdentityTesting39.ExactRadius.eq_3_scaling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:41.430494+00:00
-- url     : https://prove2.me/theorems/f3ca168f-f81e-46de-95f7-4152af1a7d99
-- title:
--   §3, (3) — compact minima, scaling and the positive real root
-- statement:
--   For $q\in[0,1]$, both $T_q(r)=(r-q)^2/(r+q)$ and $\Phi_q(w)=w^2/(q^2+w)$ are convex on the nonnegative half-line. At a nonempty strict radius, each applicable feasible branch has a compact convex moment set, an attained positive minimum for every real $n>0$, and a value continuous in $n$.
--
--   Writing $G_n$ for any such branch value,
--
--   $$c^2G_n\le G_{cn}\le cG_n\ (0<c\le1),\qquad CG_n\le G_{Cn}\le C^2G_n\ (C\ge1).$$
--
--   Off the point mass, the root set has least element $R(q,\varepsilon,i_0)>0$. In particular its infimum is over a nonempty set and is attained. The deficit branch is included only when its feasible set is nonempty. These facts give the analytic meaning of the real sample root.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - reading: relabel a largest atom → the root and its bounds are quantified over every largest label; reason: no tie-breaking rule is specified; every choice is retained
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.4, §3, display (3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_MomentPrograms

namespace IdentityTesting39.ExactRadius

/-- §3, (3), printed p.4 / PDF p.5. The deficit branch is asserted only if feasible. -/
theorem eq_3_scaling :
    (∀ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 →
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (triangularCost q) ∧
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (collisionCost q)) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε : ℝ) (B : Branch ι),
      ProbabilityVector q → StrictRadius q ε → InRegime q B → (feasibleMoments q ε B).Nonempty →
      IsCompact (feasibleMoments q ε B) ∧ Convex ℝ (feasibleMoments q ε B) ∧
      ContinuousOn (fun n => programValue q ε n B) (Set.Ioi (0 : ℝ)) ∧
      ∀ n : ℝ, 0 < n →
        (∃ x ∈ feasibleMoments q ε B, objective q B n x = programValue q ε n B) ∧
        0 < programValue q ε n B ∧
        (∀ c : ℝ, 0 < c → c ≤ 1 →
          c^2*programValue q ε n B ≤ programValue q ε (c*n) B ∧
          programValue q ε (c*n) B ≤ c*programValue q ε n B) ∧
        (∀ C : ℝ, 1 ≤ C →
          C*programValue q ε n B ≤ programValue q ε (C*n) B ∧
          programValue q ε (C*n) B ≤ C^2*programValue q ε n B)) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε : ℝ) (i₀ : ι),
      ProbabilityVector q → StrictRadius q ε → Largest q i₀ → q i₀ < 1 →
      IsLeast (rootSet q ε i₀) (sampleRoot q ε i₀) ∧ 0 < sampleRoot q ε i₀) := by sorry

end IdentityTesting39.ExactRadius
