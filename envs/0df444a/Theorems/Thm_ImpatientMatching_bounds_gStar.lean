-- Prove2me | Theorems.Thm_ImpatientMatching_bounds_gStar
-- name    : ImpatientMatching.bounds_gStar
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:49:29.333389+00:00
-- url     : https://prove2.me/theorems/3aa1ee91-7db2-4e58-944a-a9f70d212208
-- title:
--   With unit rewards, $W^\pi=M^\pi$ and $0\le g^*\le\Lambda/2$
-- statement:
--   In either hardness regime (Finite-Finite or Finite-Zero), set all rewards to one. Then for every admissible policy $\pi$ and every horizon $T$ the expected reward equals the expected number of matches, $\mathbb E W^\pi(T)=\mathbb E M^\pi(T)$, and on every input
--   $$0\le g^*\le \frac{\Lambda}{2},$$
--   where $\Lambda$ is the total arrival rate.
--
--   This makes $g^*$ a finite number and converts a relative error into an error measured against $\Lambda$, which is how the estimate clause of Theorem 3.2 follows from the promise problem.
--
--   Differences from the source:
--   - generalization: g∗ ≤ Λ/2 → also 0 ≤ g∗; reason: the lower bound of the preceding sentence on p.7, which holds in the unit-reward regimes; the clause is added and none is dropped
--   - encoding: W^π = M^π → E W^π(T) = E M^π(T) for every admissible policy and every T; reason: only the expectations enter (1); the expected forms are what the objective reads
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §2.2, the text after (1), p.7

import Definitions.Def_ImpatientMatching_Value

open DynStochMatching.Reward
open scoped ENNReal

namespace ImpatientMatching

/-- **Unit rewards: `W^π = M^π` and `g∗ ≤ Λ/2`.** Yan–Varma, manuscript (sha256 7b1051b6…), §2.2,
p.7: "For our hardness results, we shall set all rewards to one, i.e., `w_ij = 1` for all
`(i, j) ∈ E_G`, and so `W^π = M^π` and `g∗ ≤ Λ/2`."

**Formalization Note.** Stated on every input of both hardness regimes. `W^π = M^π` is stated for the
expectations, `E W^π(T) = E M^π(T)`, for every admissible policy and every `T`. The lower bound
`0 ≤ g∗` of the preceding sentence of p.7 is included, so that `g∗` is a finite number. -/
theorem bounds_gStar (r : Regime) (I : MatchInput) :
    (∀ π : MatchingPolicy, IsPaperPolicy (toInstance r I) π → ∀ T : ℝ,
      expectedReward (toInstance r I) π T = ((EM π T : ℝ≥0∞) : EReal)) ∧
    0 ≤ gStar (toInstance r I) ∧ gStar (toInstance r I) ≤ ((totalRate I / 2 : ℝ) : EReal) := by sorry

end ImpatientMatching
