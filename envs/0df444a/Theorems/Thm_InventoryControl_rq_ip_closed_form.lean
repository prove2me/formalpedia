-- Prove2me | Theorems.Thm_InventoryControl_rq_ip_closed_form
-- name    : InventoryControl.rq_ip_closed_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:01:31.156984+00:00
-- url     : https://prove2.me/theorems/2003c9bb-23b4-47bb-9319-418b73c9d753
-- title:
--   The $(R,Q)$ policy keeps the position at $y_0 - S_n$ until it falls to $R$, and in the band thereafter
-- statement:
--   Under compound Poisson demand with cumulative demand $S_n$ after $n$ customers, batch quantity
--   $Q \ge 1$ and initial inventory position $y_0$, the inventory position of the $(R,Q)$ policy
--   after the $n$-th demand is
--
--   $$ y_n \;=\; \begin{cases} y_0 - S_n & \text{if } y_0 - S_n \ge R + 1,\\
--      \text{the element of } \{R+1, \dots, R+Q\} \text{ congruent to } y_0 - S_n \pmod Q & \text{otherwise,}\end{cases} $$
--
--   for every outcome and every $n \ge 1$, and also at $n = 0$ when $y_0 \ge R + 1$; and the
--   $(R,Q)$ policy is the ordering rule `rqOrders`, in the sense that the general position
--   recursion `ipPath` driven by `rqOrders` reproduces $y_n$ for every $n$.
--
--   The exclusion is exactly one point. The position before any demand is $y_0$ itself. If
--   $y_0 \le R$, the policy places its first order at the first demand epoch, so at $n = 0$ the
--   position is $y_0$ and not its band representative. The book's model avoids that case: "we
--   always have $IP \ge R + 1$" (p. 74).
--
--   This is the book's description of the policy in Sect. 5.3.1 made exact: before the first order
--   the position simply decreases with demand, and from the first order on it stays in the band
--   $\{R+1, \dots, R+Q\}$, always congruent to $y_0 - S_n$ modulo $Q$ because orders are
--   multiples of $Q$. It is what identifies the $(R,Q)$ position with the reduced process $y_t'$
--   of the proof of Proposition 6.1 once the band has been entered.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 74, Sect. 5.3.1: 'Since an order is triggered as soon as the inventory position is less than or equal to R, we always have IP >= R + 1. Initially the inventory position may be arbitrarily large, but as soon as we have ordered at least once we must have IP <= R + Q'; p. 115: 'Using an (R, Q) policy the inventory position is also uniform on {R + 1, R + 2, ..., R + Q}'

import Definitions.Def_InventoryControl_rqPolicy

namespace InventoryControl

theorem rq_ip_closed_form {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (n : ℕ) (ω : Ω) :
    (0 < n ∨ R + 1 ≤ y0 →
      rqIP X R Q y0 n ω
        = (if R + 1 ≤ y0 - (X.cumDemand n ω : ℤ) then y0 - (X.cumDemand n ω : ℤ)
           else reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ))))
      ∧ ipPath X Q y0 (rqOrders X R Q y0) n ω = rqIP X R Q y0 n ω := by sorry

end InventoryControl
