-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_transportation_four_m_minus_five
-- name    : OnlineTransportation1195.Main.transportation_four_m_minus_five
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:36:03.459496+00:00
-- url     : https://prove2.me/theorems/624e805e-aa35-4c5f-b2ac-396aeccbfdb9
-- title:
--   Theorem 1.1 — deterministic (4m − 5)-competitive online transportation
-- statement:
--   For every finite real metric space, every subset of $m\ge2$ distinct garages, and arbitrary natural capacities (zero capacities allowed), there is a deterministic online policy that immediately and irrevocably assigns each of the $k=\sum_g c_g$ arriving cars to a free garage slot. A single policy works for every sequence of $k$ arrivals at arbitrary metric points, with repetitions allowed, and satisfies
--
--   $$\operatorname{cost}_A\le(4m-5)\operatorname{OPT}.$$
--
--   OPT is the true minimum over feasible assignments for the same complete sequence. There is no additive constant. The statement includes $k=0$, zero OPT, and metric spaces with many more points than garages. The policy is chosen before future arrivals are quantified; its feasibility and causality do not assume competitiveness.
--
--   Differences from the source:
--   - encoding: capacitated garage assignments and immediate irrevocable deterministic decisions → Fin n metric points, zero-based arrival times, slot permutations and a full-sequence function with equal-prefix garage causality; reason: all k cars fill all slots; slot labels carry no cost and causality gives a single feasible online rule on every sequence
--   - encoding: worst-case competitive ratio against the offline optimum → the multiplicative cost inequality, including zero offline optimum; reason: avoids division by zero and states the same competitive guarantee without an additive term
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Theorem 1.1, PDF / printed p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_OnlinePolicy

namespace OnlineTransportation1195.Main

theorem transportation_four_m_minus_five (n : ℕ) (I : TransportationInstance n)
    (hm : 2 ≤ I.garages.card) :
    ∃ A : Policy I, IsCausal I A ∧
      Competitive I A (4 * (I.garages.card : ℝ) - 5) := by sorry

end OnlineTransportation1195.Main
