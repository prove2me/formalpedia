-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_contracting_small_imp
-- name    : GenCoupling.Ergodic.contracting_small_imp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:00.107007+00:00
-- url     : https://prove2.me/theorems/5c2fd78f-452b-459d-9564-46e3b50b503a
-- title:
--   Remark after Definition 2.2, p. 6 — d contracting for P_t and B d-small for P_t give (2.3) and (2.4) at t
-- statement:
--   Let $(E,\rho)$ be a Polish space, $\{P_t\}$ a Markov semigroup, $t\ge0$, $d$ a distance-like function and $B\subset E$. If $d$ is contracting for $P_t$ (Definition 2.1) and $B$ is $d$-small for $P_t$ (Definition 2.2), then
--   $$W_d(P_t(x,\cdot),P_t(y,\cdot))\le d(x,y)\quad(x,y\in E),\qquad(2.3)$$
--   and there is $\varepsilon>0$ with
--   $$W_d(P_t(x,\cdot),P_t(y,\cdot))\le(1-\varepsilon)\,d(x,y)\quad(x,y\in B).\qquad(2.4)$$
--
--   The paper states this for $B=\{V\le M\}$ as the bridge from Definitions 2.1–2.2 to conditions 3 and 4 of Proposition 2.1.
--
--   **Formalization Note** Proposition 2.1 asks for (2.3) on an interval $[t_1,t_2]$ and (2.4) at one time; the remark is stated here at the single time $t$ at which both hypotheses hold, and for an arbitrary set $B$.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 6, sentence after Definition 2.2

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Remark after Definition 2.2, p. 6: if `d` is contracting for `P_t` and `B` is `d`-small for
`P_t`, then (2.3) `W_d(P_t(x,·), P_t(y,·)) ≤ d(x,y)` for all `x, y`, and (2.4)
`W_d(P_t(x,·), P_t(y,·)) ≤ (1 - ε) d(x,y)` on `B` for some `ε > 0`, at that `t`. -/
theorem contracting_small_imp {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P) (t : ℝ≥0) (d : E → E → ℝ) (B : Set E)
    (hc : IsContracting P t d) (hs : IsSmall P t d B) :
    (∀ x y, W d (P t x) (P t y) ≤ ENNReal.ofReal (d x y)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ B, ∀ y ∈ B,
        W d (P t x) (P t y) ≤ ENNReal.ofReal ((1 - ε) * d x y) := by sorry

end GenCoupling.Ergodic
