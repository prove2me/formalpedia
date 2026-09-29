-- Prove2me | Theorems.Thm_MetricTSP_held_karp_le_opt
-- name    : MetricTSP.held_karp_le_opt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:36:05.911109+00:00
-- url     : https://prove2.me/theorems/e9f760b0-792d-4b8f-b078-cd7f6d865111
-- title:
--   The Held--Karp bound is a valid relaxation: $\mathrm{LP} \le \mathrm{OPT}$
-- statement:
--   For every metric TSP instance on $n \ge 3$ cities, the Held--Karp bound is at most the optimal tour cost. The proof is that the incidence vector of any tour is a feasible point of the relaxation with objective equal to the tour's cost: it is symmetric with entries in $\{0,1\}$, every city has exactly two incident tour edges, and a Hamiltonian cycle crosses every nontrivial cut at least twice. This is the statement that makes `hkValue` a lower bound — the sense in which the LP "relaxes" the TSP.
-- source:
--   Immediate from the definitions; explicit in Held--Karp, Oper. Res. 18 (1970), and any textbook treatment, e.g. Traub--Vygen, CUP 2024, Chapter 2

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem held_karp_le_opt (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    hkValue c ≤ tspOpt c := by sorry

end MetricTSP
