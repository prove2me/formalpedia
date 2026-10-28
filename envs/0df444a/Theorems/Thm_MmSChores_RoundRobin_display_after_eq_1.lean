-- Prove2me | Theorems.Thm_MmSChores_RoundRobin_display_after_eq_1
-- name    : MmSChores.RoundRobin.display_after_eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:36.585985+00:00
-- url     : https://prove2.me/theorems/c3c7887c-f957-465e-868a-0b290ebc81c3
-- title:
--   Display after (1), proof of Theorem 9 — d_i(S_i) ≥ (1/N)·d_i(M) + (1 − 1/N)·d_i^min
-- statement:
--   Let $N\ge 1$ agents have additive utilities $d_i$ over a nonempty finite set $\mathcal M$ of chores with $d_i(j)\le 0$ for all $i$ and $j$, and let $(S_1,\dots,S_N)$ be the allocation produced by a run of the greedy round-robin protocol (Algorithm 1), under any tie-breaking rule. With $d_i^{\min}=\min_{j\in\mathcal M} d_i(j)$, every agent $i$ satisfies
--   $$d_i(S_i)\ \ge\ \frac1N\cdot d_i(\mathcal M)+\Big(1-\frac1N\Big)\cdot d_i^{\min}.$$
--
--   This averaged form of eq. (1) bounds an agent's round-robin bundle by her proportional share plus a correction of at most $(1-\tfrac1N)$ times her worst chore; together with the two upper bounds on the max-min share it yields Theorem 9.
--
--   **Formalization Note** As for eq. (1): the run is any `σ` with `IsRoundRobinRun d σ`, $S_i$ is `rrBundle σ i`, $d_i(\mathcal M)$ is `bval d i univ`, and $d_i^{\min}$ is `Finset.univ.inf' hm (d i)`. The factor $1/N$ is the real number `1 / (N : ℝ)`.
--
--   Differences from the source:
--   - generalization: chores instance (d_i(j) ≤ 0 and d_i ≢ 0) → only d_i(j) ≤ 0 for all i, j; reason: the condition d_i ≢ 0 is not used, and every chores instance satisfies the Lean hypotheses
--   - encoding: M nonempty, implicit in d_i^min = min_{j∈M} d_i(j) → explicit hypothesis that the chore set is nonempty; reason: the minimum is defined only on a nonempty set
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 4, proof of Theorem 9, display after eq. (1)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MmSChores_RoundRobin_Setting

namespace MmSChores.RoundRobin

open Finset

/-- Display after (1), proof of Theorem 9 (PDF p. 4): in every round-robin run on non-positive
utilities, `d_i(S_i) ≥ (1/N) · d_i(M) + (1 - 1/N) · d_i^min` for every agent `i`. -/
theorem display_after_eq_1 {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (hd : ∀ i j, d i j ≤ 0) (σ : Fin m ≃ Fin m)
    (hσ : IsRoundRobinRun d σ) (i : Fin N) :
    (1 / (N : ℝ)) * bval d i univ + (1 - 1 / (N : ℝ)) * univ.inf' hm (d i)
      ≤ bval d i (rrBundle σ i) := by sorry

end MmSChores.RoundRobin
