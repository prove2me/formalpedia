-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_W_comp_le
-- name    : GenCoupling.Ergodic.W_comp_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:02.469474+00:00
-- url     : https://prove2.me/theorems/65740d1b-7538-4d48-94db-28833a77d5c4
-- title:
--   Proof of Theorem 2.5, p. 10 — if W_d(P_s(u,·),P_s(v,·)) ≤ d(u,v) for all u, v then W_d at time t+s ≤ W_d at time t
-- statement:
--   Let $(E,\rho)$ be a Polish space, $\{P_t\}$ a Markov semigroup and $d$ a bounded distance-like function. Suppose that for some $s\ge0$
--   $$W_d(P_s(u,\cdot),P_s(v,\cdot))\le d(u,v)\qquad\text{for all }u,v\in E.$$
--   Then for all $t\ge0$ and $x,y\in E$,
--   $$W_d(P_{t+s}(x,\cdot),P_{t+s}(y,\cdot))\le W_d(P_t(x,\cdot),P_t(y,\cdot)).$$
--
--   In the proof of Theorem 2.5 this is the first inequality of the display $W_{d_N}(P_{t_0+t_*}(x,\cdot),P_{t_0+t_*}(y,\cdot))\le W_{d_N}(P_{t_0}(x,\cdot),P_{t_0}(y,\cdot))\le 1-\varepsilon$, obtained from (2.9) and the semigroup property; the proof of Theorem 2.6 uses it in the same way.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 10, proof of Theorem 2.5, last display, first inequality ("using (2.9) and d_N–small property")

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- First inequality of the last display of the proof of Theorem 2.5, p. 10: if
`W_d(P_s(u,·), P_s(v,·)) ≤ d(u,v)` for all `u, v` (as in (2.9)), then
`W_d(P_{t+s}(x,·), P_{t+s}(y,·)) ≤ W_d(P_t(x,·), P_t(y,·))` for all `t, x, y`. -/
theorem W_comp_le {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P)
    (d : E → E → ℝ) (hd : IsDistanceLike d) (hdb : ∃ C : ℝ, ∀ x y, d x y ≤ C) (s : ℝ≥0)
    (hne : ∀ u v, W d (P s u) (P s v) ≤ ENNReal.ofReal (d u v)) :
    ∀ (t : ℝ≥0) (x y : E), W d (P (t + s) x) (P (t + s) y) ≤ W d (P t x) (P t y) := by sorry

end GenCoupling.Ergodic
