-- Prove2me | Theorems.Thm_InventoryControl_rq_policy_cost
-- name    : InventoryControl.rq_policy_cost
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:05:33.476744+00:00
-- url     : https://prove2.me/theorems/097324be-23e6-4ee8-bd9c-128c36d08001
-- title:
--   The $(R,Q)$ policy attains the long-run cost $\bar g(R)/Q$
-- statement:
--   The second half of Proposition 6.1. Under compound Poisson demand with the aperiodicity
--   assumption, with orders in batches of $Q \ge 1$, lead-time $L \ge 0$, lead-time demand law
--   $D$ equal to the distribution of the demand over an interval of length $L$, and cost rate $g$
--   with $h, b_1 > 0$, the $(R,Q)$ policy started from any $y_0$ has long-run average cost
--   exactly $\bar g(R)/Q$: almost surely
--
--   $$ \frac{1}{T}\int_0^T g\big(y_{t-L}\big)\,\mathrm{d}t \;\longrightarrow\;
--      \frac{1}{Q}\sum_{j=1}^{Q} g(R+j) \qquad (T \to \infty), $$
--
--   where $y_t$ is the position under the $(R,Q)$ policy. This is Eq. (6.4) with the ordering
--   cost $A$ set to $0$, and it holds for every reorder point $R$, not only the minimizer of
--   $\bar g$; combined with the lower bound it gives Proposition 6.1.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 115, Sect. 6.2.1, proof of Proposition 6.1: 'But this lower bound can be achieved by using an (R, Q) policy. Using an (R, Q) policy the inventory position is also uniform on {R + 1, R + 2, ..., R + Q}. (We obtain the costs by setting A = 0 in Eq. (6.4).)'

import Definitions.Def_InventoryControl_rqPolicy

namespace InventoryControl

theorem rq_policy_cost {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (D : DiscreteDemand)
    (h b1 L : ℝ) (hh : 0 < h) (hb : 0 < b1) (hL : 0 ≤ L)
    (hD : ∀ j : ℕ, D.p j = P.real {ω | X.cumDemand (X.count L ω) ω = j})
    (Q : ℕ) (hQ : 0 < Q) (R : ℤ) (y0 : ℤ) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun T => avgCost X D h b1 L Q y0 (rqOrders X R Q y0) T ω)
      Filter.atTop (nhds (windowCost D h b1 Q R / Q)) := by sorry

end InventoryControl
