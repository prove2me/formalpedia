-- Prove2me | Theorems.Thm_MmSChores_RoundRobin_mms_le_dmin
-- name    : MmSChores.RoundRobin.mms_le_dmin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:30.422501+00:00
-- url     : https://prove2.me/theorems/1c2f5781-249b-4fb3-9242-b0e30149ced0
-- title:
--   Proof of Theorem 9, last sentence (second half) — d_i^min ≥ MmS^N_{d_i}(M) for chores
-- statement:
--   Let $N\ge 1$ agents have additive utilities over a nonempty finite set $\mathcal M$ of items, and let agent $i$'s utilities be non-positive: $d_i(j)\le 0$ for every $j\in\mathcal M$. With $d_i^{\min}=\min_{j\in\mathcal M} d_i(j)$ and $\mathrm{MmS}^N_{d_i}(\mathcal M)$ her max-min share over all allocations into $N$ (possibly empty) bundles,
--   $$d_i^{\min}\ \ge\ \mathrm{MmS}^N_{d_i}(\mathcal M).$$
--
--   For chores, no allocation can give every bundle more than the worst single chore. Together with the proportional-share bound and the averaged form of eq. (1) it gives Theorem 9.
--
--   **Formalization Note** $d_i^{\min}$ is `Finset.univ.inf' hm (d i)` and the max-min share is `LittleCharity.MMS.mms (bval d i) N univ`.
--
--   Differences from the source:
--   - generalization: in every chores setting (all agents, d_i(j) ≤ 0, d_i ≢ 0) → only agent i's utilities are non-positive, and d_i ≢ 0 is dropped; reason: the bound for agent i uses only her own signs; chores instances satisfy the hypotheses
--   - encoding: M nonempty, implicit in d_i^min = min_{j∈M} d_i(j) → explicit hypothesis that the chore set is nonempty; reason: the minimum is defined only on a nonempty set
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 4, proof of Theorem 9, sentence after the display after eq. (1)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MmSChores_RoundRobin_Setting

namespace MmSChores.RoundRobin

open Finset

/-- Proof of Theorem 9 (PDF p. 4), second half of the last sentence: `d_i^min ≥ MmS^N_{d_i}(M)`
when all of agent `i`'s utilities are non-positive. -/
theorem mms_le_dmin {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (i : Fin N) (hd : ∀ j, d i j ≤ 0) :
    LittleCharity.MMS.mms (bval d i) N univ ≤ univ.inf' hm (d i) := by sorry

end MmSChores.RoundRobin
