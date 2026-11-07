-- Prove2me | Theorems.Thm_MinSumClust_observation_39
-- name    : MinSumClust.observation_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:03.491565+00:00
-- url     : https://prove2.me/theorems/c0a516ed-c969-4912-bddb-04b638cd983c
-- title:
--   Observation 39 — dual feasibility reduces to $\Gamma$-critical clusters
-- statement:
--   Let $d$ be a distance with $d(i,i)=0$ and $d(i,j)=d(j,i)$, let $\alpha$ be a real vector and $f,\Gamma$ real numbers. If every $\Gamma$-critical cluster $C$ satisfies $\sum_{i\in C}\alpha_i\le f+\Gamma\cdot\mathrm{cost}(C)$, then every finite set $C$ does:
--
--   $$\sum_{i\in C}\alpha_i\ \le\ f+\Gamma\cdot\mathrm{cost}(C).$$
--
--   Together with Lemma 47 it proves Lemma 17.
--
--   Differences from the source:
--
--   - generalization: the final dual solution α* of Algorithm 3, f > 0, Γ = r_S γ_DC and a metric d → any real vector α, any reals f and Γ, and any d with zero diagonal and symmetry; reason: the induction on |C| uses only these two properties of d and no sign of f or Γ; α*, f > 0, Γ > 0 and metrics are special cases
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Observation 39, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsCritical

namespace MinSumClust

/-- **Observation 39 (reduction to critical clusters)**, p.34 (PDF p.36).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Observation 39, p.34.

If every Γ-critical cluster `C` satisfies `∑_{i ∈ C} α_i ≤ f + Γ · cost(C)`, then every cluster `C`
does.

**Formalization Note.** Stated for any vector `α`, any `f`, `Γ` and any distance with `d(i, i) = 0`
and `d(i, j) = d(j, i)` (the paper states it for the final dual solution `α*`). -/
theorem observation_39 {D : Type*} [DecidableEq D] (d : D → D → ℝ) (hd0 : ∀ i, d i i = 0)
    (hds : ∀ i j, d i j = d j i) (α : D → ℝ) (f Γ : ℝ)
    (h : ∀ C : Finset D, IsCritical d α Γ C → ∑ i ∈ C, α i ≤ f + Γ * cost d C) :
    ∀ C : Finset D, ∑ i ∈ C, α i ≤ f + Γ * cost d C := by sorry

end MinSumClust
