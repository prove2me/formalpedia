-- Prove2me | Theorems.Thm_GBFPlus_OccupancyDisclosure_history_invariants
-- name    : GBFPlus.OccupancyDisclosure.history_invariants
-- status  : Proved
-- author  : @queelius
-- created : 2026-10-23T18:32:31.353761+00:00
-- url     : https://prove2.me/theorems/1105332b-feaa-40fd-af3c-09da8249d281
-- title:
--   Honest histories preserve occupancy and successful row equations
-- statement:
--   For every valid configuration and every finite honest insertion history starting from the empty array, the final occupied set is exactly the union of the successful rows' position sets. Every successful row still XORs to its original target in the final snapshot, even when later insertions overlap it. Also, for any snapshot, an admissible failed attempt leaves it unchanged. Failed attempts do not contribute to the successful-row list or its length. These invariants follow from the residual update and reuse of occupied words; they are not assumptions in the definition of an honest history.
-- source:
--   Alexander Richard Towell, Adjacent-Domain Disclosure from Public Occupancy in GBFPlus, archival preprint v1.0.0, 20 October 2026, Section 2, DOI 10.5281/zenodo.23497466. Original analyzed protocol: Qin, Zhou, Dai, Sun and Qiang, Entropy 28 (2026), 947, DOI 10.3390/e28090947, Algorithm 4 and Sections 5.1–5.2. The source note is CC-BY-4.0; this new Lean formalization retains attribution and is prepared for the platform public-contribution terms. Section 2, construction paragraph immediately after Eq.(1), including its stated consequences.

import Mathlib
import Definitions.Def_GBFPlus_OccupancyDisclosure

namespace GBFPlus.OccupancyDisclosure

theorem history_invariants (C : Config) (es : List (Attempt C))
    (h : Honest (empty C) es) :
    occupied (finalSnapshot es) = supportUnion (successful es) ∧
    (∀ r ∈ successful es, rowXor (finalSnapshot es) r = r.target) ∧
    (∀ (A : Snapshot C) (e : Attempt C), admissible A e →
      e.pivot = none → step A e = A) := by sorry

end GBFPlus.OccupancyDisclosure
