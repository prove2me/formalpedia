-- Prove2me | Theorems.Thm_MetricTSP_three_paths_cert_objective
-- name    : MetricTSP.three_paths_cert_objective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T20:12:42.160883+00:00
-- url     : https://prove2.me/theorems/b42fb631-00c8-4d65-a9ac-9bb411a68c11
-- title:
--   The certificate's LP objective is at most 3k+3
-- statement:
--   The Held--Karp objective of the classical fractional certificate of the three-parallel-paths instance is at most $3k + 3$:
--   $$\tfrac12 \sum_u \sum_v c(u,v)\,x_{uv} \;\le\; 3k+3 .$$
--
--   Indeed the certificate is supported on pairs at distance $1$ (the path and hub edges) and the six equal-position pairs at distance $2$ with weight $1/6$; its total mass is $2n$ by the degree constraints, giving $n = 3k+2$ from the distance-$1$ part, plus $1$ from the distance-$2$ pairs. Combined with feasibility, this bounds the Held--Karp value of the instance by $3k+3$, the numerator of the $4/3$ gap computation.
-- source:
--   M. X. Goemans, Worst-case comparison of valid inequalities for the TSP, Mathematical Programming 69 (1995) 335-349, Section 4 (the subtour LP value of the three-path family is 3k + O(1)).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

namespace MetricTSP

theorem three_paths_cert_objective (k : ℕ) (hk : 2 ≤ k) :
    (1 / 2) * ∑ u, ∑ v, tpCost k u v * tpCert k u v ≤ 3 * k + 3 := by sorry

end MetricTSP
