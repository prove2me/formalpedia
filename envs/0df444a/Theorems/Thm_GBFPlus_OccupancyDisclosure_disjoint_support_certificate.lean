-- Prove2me | Theorems.Thm_GBFPlus_OccupancyDisclosure_disjoint_support_certificate
-- name    : GBFPlus.OccupancyDisclosure.disjoint_support_certificate
-- status  : Proved
-- author  : @queelius
-- created : 2026-10-23T18:33:34.815518+00:00
-- url     : https://prove2.me/theorems/b9ff762f-f733-41ec-9cde-182d2b008cbb
-- title:
--   Occupied-count equality certifies pairwise disjoint successful supports
-- statement:
--   For any finite honest history, if the final number of occupied cells equals the number of successful insertions times $\kappa$, every two distinct successful insertions have disjoint position sets. The insertion count comes from the history, rather than an independently supplied integer. This includes the empty history, whose pairwise-disjointness assertion is vacuous. It is the cardinality implication in the proof of Proposition 2; the positive-count assumption belongs to that disclosure proposition. Repeated equal supports are counted as different insertion occurrences and cannot satisfy pairwise disjointness since $\kappa\ge1$.
-- source:
--   Alexander Richard Towell, Adjacent-Domain Disclosure from Public Occupancy in GBFPlus, archival preprint v1.0.0, 20 October 2026, Section 2, DOI 10.5281/zenodo.23497466. Original analyzed protocol: Qin, Zhou, Dai, Sun and Qiang, Entropy 28 (2026), 947, DOI 10.3390/e28090947, Algorithm 4 and Sections 5.1–5.2. The source note is CC-BY-4.0; this new Lean formalization retains attribution and is prepared for the platform public-contribution terms. Section 2, first sentence of the proof of Proposition 2: equality in the union-cardinality bound.

import Mathlib
import Definitions.Def_GBFPlus_OccupancyDisclosure

namespace GBFPlus.OccupancyDisclosure

theorem disjoint_support_certificate (C : Config) (es : List (Attempt C))
    (h : Honest (empty C) es)
    (hcount : (occupied (finalSnapshot es)).card = (successful es).length * C.shares) :
    (successful es).Pairwise (fun r s => Disjoint r.support s.support) := by sorry

end GBFPlus.OccupancyDisclosure
