-- Prove2me | Theorems.Thm_MmSChores_RoundRobin_tight_instance_mms
-- name    : MmSChores.RoundRobin.tight_instance_mms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:59.027983+00:00
-- url     : https://prove2.me/theorems/fb072654-ffc6-4a05-88aa-6fd2c718ba72
-- title:
--   Tight instance, proof of Theorem 9 — it is a chores instance and every agent's max-min share is −1
-- statement:
--   Fix $N\ge 1$ and consider the tight instance of Theorem 9: $(N-1)N+1$ chores, of which $(N-1)N$ are worth $-\tfrac1N$ and one is worth $-1$, with the same utility function $d$ for all $N$ agents. Then this is a chores instance, and every agent's max-min share is
--   $$\mathrm{MmS}^N_{d}(\mathcal M)=-1.$$
--
--   The paper asserts that this instance shows the factor $2-\tfrac1N$ cannot be improved, without computing it; this statement is the max-min-share half of that computation.
--
--   **Formalization Note** The profile is `fun _ : Fin N => tightUtil N`, and the max-min share is `LittleCharity.MMS.mms (bval … i) N univ`, over all labelled, possibly empty, $N$-partitions of the chores.
--
--   Differences from the source:
--   - encoding: the page asserts that the instance makes the bound tight, leaving the computation implicit → the max-min share of the instance is stated explicitly as −1; reason: this is the value the tightness claim needs, stated as its own item
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 4, proof of Theorem 9, last paragraph (the computation the page leaves implicit)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MmSChores_RoundRobin_Setting
import Definitions.Def_MmSChores_RoundRobin_TightInstance

namespace MmSChores.RoundRobin

open Finset

/-- Tight instance of Theorem 9 (PDF p. 4): the profile in which every one of the `N` agents has
the utility `tightUtil N` (`(N - 1) * N` chores worth `-1/N`, one chore worth `-1`) is a chores
instance, and every agent's max-min share is `-1`. -/
theorem tight_instance_mms {N : ℕ} (hN : 0 < N) :
    IsChores (fun _ : Fin N => tightUtil N) ∧
      ∀ i : Fin N,
        LittleCharity.MMS.mms (bval (fun _ : Fin N => tightUtil N) i) N univ = -1 := by sorry

end MmSChores.RoundRobin
