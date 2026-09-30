-- Prove2me | Theorems.Thm_InventoryControl_rq_optimal_reorder_point
-- name    : InventoryControl.rq_optimal_reorder_point
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:51:37.698273+00:00
-- url     : https://prove2.me/theorems/325bc55f-2cda-4684-b865-05e76ed81079
-- title:
--   Eq. (5.67): the reorder point is cost-optimal exactly when its fill rate is $b_1/(h+b_1)$
-- statement:
--   The relationship between backorder costs and service levels that Axsäter calls "even more
--   striking" than its discrete counterpart. A continuous review $(R,Q)$ policy has a given batch
--   quantity $Q > 0$; lead-time demand is normal with mean $\mu'$ and standard deviation
--   $\sigma' > 0$; holding costs $h > 0$ per unit and time unit and backorder costs $b_1 > 0$ per
--   unit and time unit are charged on the steady-state inventory level, giving the expected cost
--   rate
--
--   $$ C(R) \;=\; \mathbb{E}\big[h\,(IL)^{+} + b_1\,(IL)^{-}\big], $$
--
--   and $S_2(R) = S_3(R) = \Pr[IL > 0]$ is the fill rate, equal to the ready rate for continuous
--   demand. The claim is that a reorder point $R$ minimizes $C$ over all real reorder points if
--   and only if
--
--   $$ S_2(R) \;=\; S_3(R) \;=\; \frac{b_1}{h + b_1} . $$
--
--   Given a backorder cost, the equation says which service level to plan for; read the other way
--   (Eq. 5.68, $b_1 = h S_2/(1 - S_2)$), a chosen fill rate reveals the backorder cost it implicitly
--   assumes. The book stresses that the equivalence holds only when $Q$ is given and the
--   optimization concerns $R$ alone; with ordering costs and a joint optimization of $R$ and $Q$
--   it fails, which is the subject of Chapter 6.
--
--   **Formalization Note** Optimality is stated as $C(R) \le C(R')$ for every real $R'$, with no
--   sign restriction on either reorder point, and the biconditional carries both directions of the
--   book's sentence: the stationary point is the optimum, and the optimum is stationary. Existence
--   and uniqueness of a reorder point with the required fill rate are not asserted here.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 86, Sect. 5.9.2, Eq. (5.67) and the sentence before it: 'The optimal R is obtained for dC/dR = 0, and in the optimal solution we have S2 = S3 = b1/(h + b1)'

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_optimal_reorder_point (h b1 R Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q)
    (hs : 0 < s) :
    (∀ R' : ℝ, rqCost h b1 R Q m s ≤ rqCost h b1 R' Q m s)
      ↔ rqReadyRate R Q m s = b1 / (h + b1) := by sorry

end InventoryControl
