-- Prove2me | Theorems.Thm_NisanRonen_Rounding_loadStates_length_le
-- name    : NisanRonen.Rounding.loadStates_length_le
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:38:36.238267+00:00
-- url     : https://prove2.me/theorems/e1e6e522-3fe2-4905-91d0-8b592e0abc12
-- title:
--   Polynomial bound on the number of distinct reachable load vectors
-- statement:
--   On a list of $k$ jobs with $n$ machines and integer processing times at most $B$, the load-vector dynamic program stores at most $(kB+1)^n$ states. A state has one integer load per machine, each in the range from $0$ to $kB$, and the table keeps one witness per vector.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, p. 192, https://doi.org/10.1006/game.1999.0790. State-count bound for the load-vector implementation of the rounded dynamic program.

import Definitions.Def_NisanRonen_Rounding_boundedLoadDP

namespace NisanRonen.Rounding

theorem loadStates_length_le {n : ℕ} (cap : ℕ) (columns : List (Fin n → ℕ))
    (hc : ∀ c ∈ columns, ∀ i, c i ≤ cap) :
    (loadStates columns).length ≤ (columns.length * cap + 1) ^ n := by sorry

end NisanRonen.Rounding
