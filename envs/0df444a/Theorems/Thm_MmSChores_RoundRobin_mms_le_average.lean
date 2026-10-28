-- Prove2me | Theorems.Thm_MmSChores_RoundRobin_mms_le_average
-- name    : MmSChores.RoundRobin.mms_le_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:37.898034+00:00
-- url     : https://prove2.me/theorems/f59bcf40-b4d5-493e-a9eb-bcad7256e29b
-- title:
--   Proof of Theorem 9, last sentence (first half) — (1/N)·d_i(M) ≥ MmS^N_{d_i}(M)
-- statement:
--   Let $N\ge 1$ agents have additive utilities $d_i$ over a finite set $\mathcal M$ of items, and let
--   $$\mathrm{MmS}^N_{d_i}(\mathcal M)=\max_{(S_1,\dots,S_N)\in\Pi_N(\mathcal M)}\ \min_{j\in[N]} d_i(S_j)$$
--   be agent $i$'s max-min share, the maximum ranging over all allocations of $\mathcal M$ into $N$ (possibly empty) bundles. Then for every agent $i$,
--   $$\frac1N\cdot d_i(\mathcal M)\ \ge\ \mathrm{MmS}^N_{d_i}(\mathcal M).$$
--
--   The max-min share never exceeds the proportional share. The paper states this "in every chores setting"; it holds for arbitrary real additive utilities.
--
--   **Formalization Note** The max-min share is the published `LittleCharity.MMS.mms (bval d i) N univ`, a supremum over labelled maps `Fin m → Fin N` (bundles may be empty) of the minimum bundle value; for `N ≥ 1` both index types are finite and nonempty, so it is the true max-min.
--
--   Differences from the source:
--   - generalization: in every chores setting (d_i(j) ≤ 0, d_i ≢ 0) → arbitrary real utilities d_i, no sign condition; reason: the inequality holds for every additive utility and specializes to chores instances
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 4, proof of Theorem 9, sentence after the display after eq. (1)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MmSChores_RoundRobin_Setting

namespace MmSChores.RoundRobin

open Finset

/-- Proof of Theorem 9 (PDF p. 4), first half of the last sentence: `1/N · d_i(M) ≥ MmS^N_{d_i}(M)`.
It holds for every real additive utility, with no sign condition. -/
theorem mms_le_average {N m : ℕ} (hN : 0 < N) (d : Fin N → Fin m → ℝ) (i : Fin N) :
    LittleCharity.MMS.mms (bval d i) N univ ≤ (1 / (N : ℝ)) * bval d i univ := by sorry

end MmSChores.RoundRobin
