-- Prove2me | Theorems.Thm_InventoryControl_reduced_cost_average
-- name    : InventoryControl.reduced_cost_average
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:03:25.551261+00:00
-- url     : https://prove2.me/theorems/0d26653f-7330-4eaf-8228-60de6cbbf68e
-- title:
--   The long-run average of $g(y_t')$ is $\bar g(R)/Q$
-- statement:
--   In the setting of Proposition 6.1 (compound Poisson demand with the aperiodicity assumption,
--   batch quantity $Q \ge 1$, reorder point $R$, initial position $y_0$, lead-time $L \ge 0$), let
--   $y_t'$ be the reduction modulo $Q$ of $y_0 - S_{N(t)}$ into $\{R+1, \dots, R+Q\}$ and let
--   $g$ be the cost rate of the discrete lead-time demand. Then almost surely
--
--   $$ \frac{1}{T}\int_0^T g\big(y'_{t-L}\big)\,\mathrm{d}t \;\longrightarrow\;
--      \frac{\bar g(R)}{Q} \;=\; \frac{1}{Q}\sum_{j=1}^{Q} g(R + j) \qquad (T \to \infty), $$
--
--   with $y'_s = y_0$ for $s < 0$.
--
--   It is the uniform occupation of the band applied to the bounded function $g$ on it, together
--   with the observation that the lead-time shift and the initial segment before time $0$ do not
--   affect a long-run average. The book states it in one sentence and it is the number that every
--   policy's cost is compared against.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 115, Sect. 6.2.1: 'The long-run average value of g(y't) is therefore g-bar(R)/Q'

import Definitions.Def_InventoryControl_rqPolicy

namespace InventoryControl

theorem reduced_cost_average {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (D : DiscreteDemand)
    (h b1 L : ℝ) (hL : 0 ≤ L) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
          sPolicyCost D h b1 (if t < L then y0
            else reduceToBand R Q (y0 - (X.cumDemand (X.count (t - L) ω) ω : ℤ))))
      Filter.atTop (nhds (windowCost D h b1 Q R / Q)) := by sorry

end InventoryControl
