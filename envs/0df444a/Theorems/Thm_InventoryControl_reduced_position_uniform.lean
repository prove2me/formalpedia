-- Prove2me | Theorems.Thm_InventoryControl_reduced_position_uniform
-- name    : InventoryControl.reduced_position_uniform
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:02:56.299769+00:00
-- url     : https://prove2.me/theorems/4041f791-4404-4fa8-b2bf-de863e0e9641
-- title:
--   The reduced position $y_t'$ spends a fraction $1/Q$ of the time at each point of the band
-- statement:
--   Under compound Poisson demand whose demand sizes are not all multiples of some integer larger
--   than one, fix a batch quantity $Q \ge 1$, a reorder point $R$ and an initial position $y_0$,
--   and let $y_t' \in \{R+1, \dots, R+Q\}$ be the reduction modulo $Q$ of $y_0 - S_{N(t)}$, where
--   $S_{N(t)}$ is the total demand by time $t$. Then for every $j \in \{R+1, \dots, R+Q\}$, almost
--   surely,
--
--   $$ \frac{1}{T}\int_0^T \mathbf{1}\{y_t' = j\}\,\mathrm{d}t \;\longrightarrow\; \frac{1}{Q}
--      \qquad (T \to \infty). $$
--
--   This is the ergodic form of "the steady state distribution is uniform". The process $y_t'$ is
--   the same for every ordering rule, because every policy's position is congruent to
--   $y_0 - S_{N(t)}$ modulo $Q$, and it is a continuous-time random walk on the $Q$ residues
--   driven by the demand sizes; the aperiodicity assumption makes that walk irreducible, and the
--   uniform distribution is stationary because the walk is doubly stochastic (the argument of
--   Proposition 5.1, Eq. 5.33-5.34). The long-run time average of any function of $y_t'$ is then
--   its average over the band.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 115, Sect. 6.2.1: 'The demand sizes are independent, so the different y't can be seen as a Markov chain with the finite state space {R + 1, R + 2, ..., R + Q}. The steady state distribution can be shown to be uniform'; the argument is that of Proposition 5.1, p. 74

import Definitions.Def_InventoryControl_rqPolicy

namespace InventoryControl

theorem reduced_position_uniform {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ)
    (hQ : 0 < Q) (y0 : ℤ) (j : ℤ) (hj1 : R + 1 ≤ j) (hj2 : j ≤ R + Q) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
          (if reduceToBand R Q (y0 - (X.cumDemand (X.count t ω) ω : ℤ)) = j then (1 : ℝ) else 0))
      Filter.atTop (nhds (1 / (Q : ℝ))) := by sorry

end InventoryControl
