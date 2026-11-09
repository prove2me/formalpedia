-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_eq_7_tv_branches
-- name    : IdentityTesting39.ExactRadius.eq_7_tv_branches
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:45.484858+00:00
-- url     : https://prove2.me/theorems/86acd08d-5216-46b1-b623-132b365cc7cd
-- title:
--   §4, (7) — total variation and the two head-deleted branches
-- statement:
--   Let $p,q$ be probability vectors on a finite domain and omit any label $i_0$. Then
--
--   $$\operatorname{TV}(p,q)=\max\left\{\sum_{i\ne i_0}(q_i-p_i)_+,\sum_{i\ne i_0}(p_i-q_i)_+\right\}.$$
--
--   Every vector at distance at least $\varepsilon$ has a deterministic tuple feasible in at least one closed head-deleted branch. If the distance strictly exceeds $\varepsilon$, at least one of these tail sums strictly exceeds it as well. The omitted label need not be largest. This identity justifies using both branches to cover every strict alternative.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - encoding: p lies in a branch → the deterministic tuple is explicitly formed from p and its unused head slots set to zero; reason: this spells out the witness rather than quantifying an unrelated tuple
--   - generalization: the head-deleted identity with a largest reference atom and positive testing radius → any omitted label and branch coverage for every real threshold; reason: the omitted coordinate contributes only one sign, so the maximum of the two tail sums equals full TV; choosing the source head and radius recovers every source instance
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.5, §4, display (7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_MomentPrograms

open scoped BigOperators

namespace IdentityTesting39.ExactRadius

/-- §4, (7), printed p.5 / PDF p.6, for any omitted label. -/
theorem eq_7_tv_branches {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (i₀ : ι) (hp : ProbabilityVector p) (hq : ProbabilityVector q) :
    FoundationsRL.GeneralDM.totalVariationDiscrete p q = max (∑ i ∈ Finset.univ.erase i₀, max (q i-p i) 0)
      (∑ i ∈ Finset.univ.erase i₀, max (p i-q i) 0) ∧
    (∀ ε : ℝ, ε ≤ FoundationsRL.GeneralDM.totalVariationDiscrete p q →
      deterministicTuple q p (.excess i₀) ∈ feasibleMoments q ε (.excess i₀) ∨
      deterministicTuple q p (.deficit i₀) ∈ feasibleMoments q ε (.deficit i₀)) ∧
    (∀ ε : ℝ, ε < FoundationsRL.GeneralDM.totalVariationDiscrete p q →
      (ε < ∑ i ∈ Finset.univ.erase i₀, max (p i-q i) 0) ∨
      (ε < ∑ i ∈ Finset.univ.erase i₀, max (q i-p i) 0)) := by sorry

end IdentityTesting39.ExactRadius
