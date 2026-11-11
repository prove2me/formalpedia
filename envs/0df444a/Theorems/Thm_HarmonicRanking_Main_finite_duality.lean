-- Prove2me | Theorems.Thm_HarmonicRanking_Main_finite_duality
-- name    : HarmonicRanking.Main.finite_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:17.983823+00:00
-- url     : https://prove2.me/theorems/a81c6f6f-478f-4c69-81e4-2ac117ec0158
-- title:
--   Proposition 5.1 — exact finite threshold cut–flow equality
-- statement:
--   For any $m\ge1$ and positive nonincreasing real heights $H_1,\ldots,H_m$, construct the exact finite threshold network $N_m(H)$, retaining every arc record. Its maximum flow, minimum cut, and finite threshold-game minimum satisfy
--
--   $$
--   \operatorname{MF}_m(H)=\operatorname{MC}_m(H)
--   =\min_{(a,b)\in\mathcal T_m}\Gamma_m^H(a,b).
--   $$
--
--   All three extrema are attained: a feasible maximizing flow, a minimizing source shore, and a minimizing admissible threshold pair exist. No monotonicity across the entries of either threshold vector is imposed. This identifies the entire finite game with the source network, beyond generic max-flow/min-cut duality.
--
--   Differences from the source:
--   - encoding: cell indices 1 through m, threshold counts 0 through m → Fin m cell indices are shifted down by one and Fin (m+1) threshold counts are unchanged; reason: the same cells, adjacent arcs, and last-cell increments are represented bijectively
--   - encoding: maximum flow and minimum cut equal a finite minimum → supremum and infimum values are defined from actual flows, shores, and threshold payoffs, and all three attainments are explicit conclusions; reason: this retains the maximum and minimum strength and excludes any default-value interpretation of the extrema
--   - encoding: infinite implication capacities replaced by 2 in the ordinary network on p. 17 → hard arcs have finite capacity 2 from the start; reason: the source explicitly declares the equivalent finite-capacity network to be N_m(H)
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 18, Proposition 5.1

import Definitions.Def_HarmonicRanking_Main_Network

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem finite_duality {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) :
    MF H = MC H ∧ MC H = finiteGameValue H ∧
    (∃ f : StepArc m → ℝ, FeasibleFlow (stepNetwork H) f ∧
      flowValue (stepNetwork H) f = MF H) ∧
    (∃ S : Finset (StepNode m), IsShore (stepNetwork H) S ∧
      cutCapacity (stepNetwork H) S = MC H) ∧
    (∃ c : Thresholds m, discreteAdmissible c ∧ GammaFinite H c = finiteGameValue H) := by sorry

end HarmonicRanking.Main
