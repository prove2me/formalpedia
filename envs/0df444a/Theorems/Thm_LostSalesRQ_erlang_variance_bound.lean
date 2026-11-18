-- Prove2me | Theorems.Thm_LostSalesRQ_erlang_variance_bound
-- name    : LostSalesRQ.erlang_variance_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:24:09.479286+00:00
-- url     : https://prove2.me/theorems/a1df4de7-5bbf-47d9-b2a6-83e6e90846a9
-- title:
--   Eq. (A.3): Erlang variance bound
-- statement:
--   For every $\mu>0$ and every integer $j\ge1$, the variance $v_j$ of the stationary on-hand inventory of base stock $j$ satisfies
--   $$0<v_j\le H_j(H_j+1).$$
--
--   This bound between the variance and mean of on-hand inventory is used in the tightness argument and in Appendices F and H.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Appendix A.1, eq. (A.3) (p. A2).

import Definitions.Def_LostSalesRQ_poisson_functions

namespace LostSalesRQ

theorem erlang_variance_bound (μ : ℝ) (hμ : 0 < μ) (j : ℕ) (hj : 1 ≤ j) :
    0 < onHandVariance μ j ∧ onHandVariance μ j ≤ meanOnHand μ j * (meanOnHand μ j + 1) := by sorry

end LostSalesRQ
