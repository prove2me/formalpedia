-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_nearest_garage_reduction
-- name    : OnlineTransportation1195.Main.nearest_garage_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:59.467403+00:00
-- url     : https://prove2.me/theorems/c025fc34-df9f-4660-b148-0b7bdc05fd10
-- title:
--   Lemma 4.1 — nearest-garage reduction
-- statement:
--   Let $f$ assign nonnegative competitive factors to point counts. If for every $n$ there is a deterministic online guarantee of factor $f(n)$ on all $n$-point transportation instances, then there is a deterministic guarantee depending on the number $m$ of garages:
--
--   $$\operatorname{cost}_A\le(2f(m)+1)\operatorname{OPT}.$$
--
--   The conclusion covers all finite real metrics and all garage subsets and natural capacities, with a single causal policy for each static instance working on every arrival sequence. The factor uses the original garage count. Arrival locations in the original metric are unrestricted. This is an existence reduction, not a premise asserting the desired performance of a supplied auxiliary assignment.
--
--   Differences from the source:
--   - encoding: capacitated garage assignments and immediate irrevocable deterministic decisions → Fin n metric points, zero-based arrival times, slot permutations and a full-sequence function with equal-prefix garage causality; reason: all k cars fill all slots; slot labels carry no cost and causality gives a single feasible online rule on every sequence
--   - encoding: competitive ratio for the complete online problem → a nonnegative multiplicative factor and no division by OPT; reason: competitive factors have their conventional nonnegative domain; the inequality also states the zero-OPT case
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Lemma 4.1, PDF / printed p. 15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_OnlinePolicy

namespace OnlineTransportation1195.Main

theorem nearest_garage_reduction (f : ℕ → ℝ)
    (h : ∀ n : ℕ, PointRatio n (f n)) :
    GarageRatios (fun m => 2 * f m + 1) := by sorry

end OnlineTransportation1195.Main
