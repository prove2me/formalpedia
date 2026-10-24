-- Prove2me | Theorems.Thm_GBFPlus_OccupancyDisclosure_aggregate_disclosure
-- name    : GBFPlus.OccupancyDisclosure.aggregate_disclosure
-- status  : Proved
-- author  : @queelius
-- created : 2026-10-23T18:34:04.067453+00:00
-- url     : https://prove2.me/theorems/d6c7dd0b-6916-4761-8ab4-4b6b7b69f154
-- title:
--   Proposition 2: the disjoint-position certificate reveals the identifier XOR
-- statement:
--   For every honest snapshot with $c\ge1$ successful insertions and public occupied-cell count $w=c\kappa$, XORing the occupied words and taking their final $\ell$ bits yields the XOR of the $c$ inserted adjacent-domain identifiers. The successful count is derived from the insertion history. The certificate implies $c\kappa\le m$ and disjoint successful position sets. For $c>1$ the conclusion gives only this aggregate, not the individual identifiers or their multiset. The equality is a sufficient certificate, not a necessary condition for every possible disclosure; no conclusion or probability claim is made for snapshots failing it. Ledger read access, genuine occupancy and authentic honest generation remain the source interpretation's explicit premises.
-- source:
--   Alexander Richard Towell, Adjacent-Domain Disclosure from Public Occupancy in GBFPlus, archival preprint v1.0.0, 20 October 2026, Section 2, DOI 10.5281/zenodo.23497466. Original analyzed protocol: Qin, Zhou, Dai, Sun and Qiang, Entropy 28 (2026), 947, DOI 10.3390/e28090947, Algorithm 4 and Sections 5.1–5.2. The source note is CC-BY-4.0; this new Lean formalization retains attribution and is prepared for the platform public-contribution terms. Section 2, Proposition 2 (Disjoint-position certificate), Eq.(3), and scope paragraphs following its proof.

import Mathlib
import Definitions.Def_GBFPlus_OccupancyDisclosure

namespace GBFPlus.OccupancyDisclosure

theorem aggregate_disclosure (C : Config) (es : List (Attempt C))
    (h : Honest (empty C) es) (hpositive : 1 ≤ (successful es).length)
    (hcount : (occupied (finalSnapshot es)).card = (successful es).length * C.shares) :
    recover (finalSnapshot es) = identifierXor (successful es) := by sorry

end GBFPlus.OccupancyDisclosure
