-- Prove2me | Theorems.Thm_InventoryControl_rq_position_uniform
-- name    : InventoryControl.rq_position_uniform
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:04:02.050889+00:00
-- url     : https://prove2.me/theorems/686b447b-d6ef-4f61-8dd0-be0d0486db95
-- title:
--   Proposition 5.1: under the $(R,Q)$ policy the inventory position is uniform on $\{R+1,\dots,R+Q\}$
-- statement:
--   Proposition 5.1 in its ergodic form. Under compound Poisson demand whose demand sizes are not
--   all multiples of some integer larger than one, an $(R,Q)$ policy with $Q \ge 1$ started from
--   any initial inventory position $y_0$ spends, in the long run, a fraction $1/Q$ of the time at
--   each of the positions $R+1, \dots, R+Q$: for every such $j$, almost surely
--
--   $$ \frac{1}{T}\int_0^T \mathbf{1}\{y_{N(t)} = j\}\,\mathrm{d}t \;\longrightarrow\; \frac{1}{Q}
--      \qquad (T \to \infty), $$
--
--   where $y_n$ is the position after the $n$-th demand under the policy.
--
--   The book proves the proposition for the embedded chain at demand epochs by showing that the
--   transition matrix is doubly stochastic (Eq. 5.33-5.34), which makes the uniform distribution
--   stationary, and irreducibility, which comes from the aperiodicity assumption, makes it the
--   unique one. Here the statement is about time averages, which is how the proposition is used:
--   the cost of the $(R,Q)$ policy is the average of $g$ over the band. The initial position may
--   lie above the band; the policy enters the band after finitely many demands and the initial
--   segment does not affect the limit.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 74, Sect. 5.3.1, Proposition 5.1: 'In steady state the inventory position is uniformly distributed on the integers R + 1, R + 2, ..., R + Q'; used on p. 115: 'Using an (R, Q) policy the inventory position is also uniform on {R + 1, R + 2, ..., R + Q}'

import Definitions.Def_InventoryControl_rqPolicy

namespace InventoryControl

theorem rq_position_uniform {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ)
    (hQ : 0 < Q) (y0 : ℤ) (j : ℤ) (hj1 : R + 1 ≤ j) (hj2 : j ≤ R + Q) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
          (if rqIP X R Q y0 (X.count t ω) ω = j then (1 : ℝ) else 0))
      Filter.atTop (nhds (1 / (Q : ℝ))) := by sorry

end InventoryControl
