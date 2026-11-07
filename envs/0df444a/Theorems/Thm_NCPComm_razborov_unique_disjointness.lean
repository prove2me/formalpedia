-- Prove2me | Theorems.Thm_NCPComm_razborov_unique_disjointness
-- name    : NCPComm.razborov_unique_disjointness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:36.625189+00:00
-- url     : https://prove2.me/theorems/010555f6-1580-48c5-8a71-695206ae110c
-- title:
--   Razborov 1992 — unique disjointness, as quoted in the proof of Theorem 3.14
-- statement:
--   There is an absolute $\kappa>0$ such that, for every $r\ge1$, every public-coin protocol that distinguishes intersection size $0$ from intersection size $1$, on sets of size $r$ in a universe of size $4r$, with error at most $\frac13$, communicates at least $\kappa r$ bits.
--
--   This is the cited lower bound on which the whole mission rests ([Raz92]; see also [She14, Section 4]).
--
--   Differences from the source:
--   - reading: "they must output 1 (accept)" (Definition 3.13), with "Alice's decision" on p.10 → only Alice's output must be correct; reason: stronger for a lower bound: a protocol where both are correct is one where Alice is; the page takes Alice's decision on p.10
--   - encoding: communication Ω(r) → κ·r ≤ k with κ > 0 absolute; reason: the meaning of Ω for an absolute lower bound; r = 1 is included because a 0-bit protocol cannot distinguish the two cases
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), proof of Theorem 3.14, p.17 (citing [Raz92])

import Mathlib
import Definitions.Def_NCPComm_SolvesExactGapDisj

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Razborov's lower bound [Raz92], as quoted in the proof of Theorem 3.14, p.17** (Herman, The
Communication Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript
sha256 714c0353…; cited result). There is an absolute `κ > 0` such that every public-coin protocol
for sets of size `r ≥ 1` in a universe of size `4r`, with intersection promised to have size `0` or
`1`, with error at most `1/3`, communicates at least `κ·r` bits.

**Formalization Note** Only Alice's output is required to be correct (`SolvesExactGapDisj`). -/
theorem razborov_unique_disjointness :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (r : ℕ), 1 ≤ r →
      ∀ (P : DistVerif.Simulation.PubProtocol (4 * r)) (k : ℕ),
        SolvesExactGapDisj P k 1 r r (1 / 3) → κ * (r : ℝ) ≤ (k : ℝ) := by sorry

end NCPComm
