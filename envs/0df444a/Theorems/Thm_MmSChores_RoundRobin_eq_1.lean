-- Prove2me | Theorems.Thm_MmSChores_RoundRobin_eq_1
-- name    : MmSChores.RoundRobin.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:24.922991+00:00
-- url     : https://prove2.me/theorems/a345f3a4-fd22-4b84-af3c-8a0d925c3e04
-- title:
--   Eq. (1), proof of Theorem 9 — under round-robin, d_i(S_i) ≥ d_i(S_i′) + d_i^min for all agents i, i′
-- statement:
--   Let $N\ge 1$ agents have additive utilities $d_i$ over a nonempty finite set $\mathcal M$ of chores with $d_i(j)\le 0$ for all $i$ and $j$, and let $(S_1,\dots,S_N)$ be the allocation produced by a run of the greedy round-robin protocol (Algorithm 1), under any tie-breaking rule. Write $d_i^{\min}=\min_{j\in\mathcal M} d_i(j)$. Then for all agents $i,i'\in[N]$,
--   $$d_i(S_i)\ \ge\ d_i(S_{i'})+d_i^{\min}.\qquad (1)$$
--
--   This is the comparison between an agent's own bundle and any other bundle, measured with her own utility, on which the $2-\tfrac1N$ guarantee of Theorem 9 rests. It holds for $i=i'$ as well, and in both pick orders of $i$ and $i'$.
--
--   **Formalization Note** Agents are `Fin N` (agent 1 is index `0`), the run is any `σ` with `IsRoundRobinRun d σ`, $S_i$ is `rrBundle σ i`, and $d_i^{\min}$ is `Finset.univ.inf' hm (d i)` for `hm` the nonemptiness of the chore set.
--
--   Differences from the source:
--   - generalization: chores instance (d_i(j) ≤ 0 and d_i ≢ 0) → only d_i(j) ≤ 0 for all i, j; reason: the condition d_i ≢ 0 is not used, and every chores instance satisfies the Lean hypotheses
--   - encoding: M nonempty, implicit in d_i^min = min_{j∈M} d_i(j) → explicit hypothesis that the chore set is nonempty; reason: the minimum is defined only on a nonempty set
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 4, proof of Theorem 9, eq. (1)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MmSChores_RoundRobin_Setting

namespace MmSChores.RoundRobin

open Finset

/-- Eq. (1), proof of Theorem 9 (PDF p. 4): in every round-robin run on non-positive utilities,
`d_i(S_i) ≥ d_i(S_{i'}) + d_i^min` for all agents `i, i'`, where
`d_i^min = min_{j ∈ M} d_i(j)`. -/
theorem eq_1 {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (hd : ∀ i j, d i j ≤ 0) (σ : Fin m ≃ Fin m)
    (hσ : IsRoundRobinRun d σ) (i i' : Fin N) :
    bval d i (rrBundle σ i') + univ.inf' hm (d i) ≤ bval d i (rrBundle σ i) := by sorry

end MmSChores.RoundRobin
