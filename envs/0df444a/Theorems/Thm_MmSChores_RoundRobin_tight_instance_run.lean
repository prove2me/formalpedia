-- Prove2me | Theorems.Thm_MmSChores_RoundRobin_tight_instance_run
-- name    : MmSChores.RoundRobin.tight_instance_run
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:38.863748+00:00
-- url     : https://prove2.me/theorems/a7928968-1b7d-4577-ad07-8dd14489eac4
-- title:
--   Tight instance, proof of Theorem 9 — every round-robin run gives agent 1 a bundle worth exactly −(2 − 1/N)
-- statement:
--   Fix $N\ge 1$ and consider the tight instance of Theorem 9: $(N-1)N+1$ chores, of which $(N-1)N$ are worth $-\tfrac1N$ and one is worth $-1$, with the same utility function $d$ for all $N$ agents. In every run of the greedy round-robin protocol (Algorithm 1), under any tie-breaking rule, agent 1 receives a bundle $S_1$ with
--   $$d(S_1)=-\Big(2-\frac1N\Big).$$
--
--   Together with the max-min share $-1$ of this instance, agent 1 receives exactly $(2-\tfrac1N)\cdot\mathrm{MmS}^N_d(\mathcal M)$, so the factor of Theorem 9 is attained.
--
--   **Formalization Note** The run is any `σ` with `IsRoundRobinRun (fun _ : Fin N => tightUtil N) σ`; agent 1 is index `⟨0, hN⟩` and $S_1$ is `rrBundle σ ⟨0, hN⟩`.
--
--   Differences from the source:
--   - encoding: the page asserts that the instance makes the bound tight, leaving the computation implicit → agent 1's round-robin value is stated explicitly as −(2 − 1/N) for every run; reason: this is the value the tightness claim needs, stated as its own item
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 4, proof of Theorem 9, last paragraph (the computation the page leaves implicit)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MmSChores_RoundRobin_Setting
import Definitions.Def_MmSChores_RoundRobin_TightInstance

namespace MmSChores.RoundRobin

open Finset

/-- Tight instance of Theorem 9 (PDF p. 4): in every round-robin run on the profile in which every
agent has the utility `tightUtil N`, agent 1 (index `0`) receives a bundle worth exactly
`-(2 - 1/N)`. -/
theorem tight_instance_run {N : ℕ} (hN : 0 < N)
    (σ : Fin ((N - 1) * N + 1) ≃ Fin ((N - 1) * N + 1))
    (hσ : IsRoundRobinRun (fun _ : Fin N => tightUtil N) σ) :
    bval (fun _ : Fin N => tightUtil N) ⟨0, hN⟩ (rrBundle σ ⟨0, hN⟩) =
      -(2 - 1 / (N : ℝ)) := by sorry

end MmSChores.RoundRobin
