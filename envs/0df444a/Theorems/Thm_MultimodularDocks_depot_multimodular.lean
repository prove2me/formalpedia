-- Prove2me | Theorems.Thm_MultimodularDocks_depot_multimodular
-- name    : MultimodularDocks.depot_multimodular
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:48.338005+00:00
-- url     : https://prove2.me/theorems/72ff2737-4396-4ca6-ad07-878e309b5756
-- title:
--   Depot station (corrected: multimodular on the quadrant) — $c_D(d,b)=d+b-B$ fulfills Definition 1
-- statement:
--   For every bike budget $B$, the depot cost
--
--   $$
--   c_D(d,b)=d+b-B
--   $$
--
--   is multimodular: inequalities (1)–(3) of Definition 1 hold (with equality) wherever all their arguments are nonnegative.
--
--   Together with Lemma 2.1 this lets the dummy depot station join the stations of problem (P2), so that the results of the mission apply to the paper's reduction from (P1) to (P2).
--
--   Differences from the source:
--   - correction: c_D = d + b − B on l_D ≤ d + b ≤ u_D, ∞ elsewhere, fulfills Definition 1 for all d, b with ∞ − ∞ = ∞ → the real function d + b − B satisfies (1)–(3) whenever all arguments are ≥ 0; reason: the printed claim is false under the printed convention: B = 0, D = 2 (l_D = 0, u_D = 2): (1) at d = −1, b = 0 reads c_D(0, 1) − c_D(0, 0) = 1 ≥ ∞ − ∞ = ∞ (paper.md item 1)
--   - encoding: c_D restricted to its band l_D ≤ d + b ≤ u_D → depotCost on all of ℤ², the band given by the station's bounds in an instance; reason: the band is part of feasibility, not of the cost function; same instances
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §2, p.12 (depot station D)

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_depotCost

namespace MultimodularDocks

/-- **The depot cost fulfills Definition 1** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, §2,
p.12: "cD(d, b) = d + b − B … observe that cD fulfills the requirements of Definition 1"). For
every `B`, `c_D(d, b) = d + b − B` is multimodular. -/
theorem depot_multimodular (B : ℤ) : IsMultimodular (depotCost B) := by sorry

end MultimodularDocks
