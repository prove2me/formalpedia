-- Prove2me | Theorems.Thm_NestedCRP_gem_sticks_sum_one
-- name    : NestedCRP.gem_sticks_sum_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:49.577306+00:00
-- url     : https://prove2.me/theorems/fc608450-5e48-43f2-b952-cee96ef97261
-- title:
--   $\mathrm{GEM}(m,\pi)$ sticks sum to one almost surely
-- statement:
--   Let $V_0,V_1,\dots$ be i.i.d. $\mathrm{Beta}(m\pi,(1-m)\pi)$ with $\pi>0$ and $m\in(0,1)$, and let $\theta_i=V_i\prod_{j<i}(1-V_j)$. Then, almost surely,
--
--   $$
--   \sum_{i\ge0}\theta_i=1.
--   $$
--
--   The paper attributes this to Sethuraman (1994). It says the level distribution of a document is a genuine distribution on the levels, so that the posterior on level allocations has the right total mass.
--
--   Differences from the source:
--   - encoding: levels and sticks are 1-based → levels and sticks are 0-based; reason: Lean indexing; level ℓ here is the paper's level ℓ + 1, and no instance changes
--   - encoding: V_i i.i.d. Beta(α1, α2) with α1, α2 > 0 (Sethuraman, p.7:7) → V_i i.i.d. Beta(mπ, (1 − m)π) with m ∈ (0,1), π > 0; reason: a bijective reparametrization (m = α1/(α1+α2), π = α1+α2); the same set of laws
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §2.3, p.7:7 and p.7:8

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_gemLaw
open MeasureTheory

namespace NestedCRP

/-- The sticks of GEM(m, π) sum to one almost surely. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010),
§2.3, p.7:7 (attributed to Sethuraman 1994) and p.7:8. -/
theorem gem_sticks_sum_one (H : Hyper) :
    ∀ᵐ U ∂gemLaw H.m H.pi, HasSum (stick U) 1 := by sorry

end NestedCRP
