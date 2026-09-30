-- Prove2me | Theorems.Thm_InventoryControl_rq_policy_lower_bound
-- name    : InventoryControl.rq_policy_lower_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:04:59.209625+00:00
-- url     : https://prove2.me/theorems/c9c067cd-3478-4f5a-8e69-664f564b52d9
-- title:
--   $\bar g(R)/Q$ is a lower bound on the long-run cost of any feasible policy
-- statement:
--   The first half of Proposition 6.1. Under compound Poisson demand with the aperiodicity
--   assumption, let orders be restricted to multiples of a batch quantity $Q \ge 1$ and be
--   triggered only by demands, let the lead-time demand distribution be that of the demand over
--   an interval of length $L \ge 0$, let $g$ be its holding-plus-shortage cost rate with
--   $h, b_1 > 0$, and let $R$ minimize $\bar g(y) = \sum_{j=1}^{Q} g(y+j)$. Then for every ordering
--   rule $m$ whatsoever and every initial position $y_0$, almost surely,
--
--   $$ \liminf_{T \to \infty}\ \frac{1}{T}\int_0^T g\big(y^{m}_{t-L}\big)\,\mathrm{d}t
--      \;\ge\; \frac{\bar g(R)}{Q}, $$
--
--   where $y^m_t$ is the inventory position under $m$.
--
--   The argument is pathwise: every policy's position is congruent modulo $Q$ to $y_0 - S_{N(t)}$,
--   so by Lemma 6.1 its cost rate is at least $g(y_t')$ at every instant, and the long-run average
--   of $g(y_t')$ is $\bar g(R)/Q$. No measurability, adaptedness or stability of the rule is
--   needed; a rule under which the position drifts to infinity simply has infinite average cost.
--
--   **Formalization Note** "$\liminf \ge c$" is written without a `liminf`: for every
--   $\varepsilon > 0$ the average eventually exceeds $c - \varepsilon$. The lead-time demand law
--   $D$ is tied to the process by the hypothesis that $D$ is the distribution of the demand in
--   $(0, L]$.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 115, Sect. 6.2.1, proof of Proposition 6.1: 'From Lemma 6.1 we know that g(yt) >= g(y't) ... Consequently, the long-run average cost must be greater than or equal to the long-run average value of g(y't) ... This is a lower bound on the long-run cost of any feasible policy'

import Definitions.Def_InventoryControl_rqPolicy

namespace InventoryControl

theorem rq_policy_lower_bound {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (D : DiscreteDemand)
    (h b1 L : ℝ) (hh : 0 < h) (hb : 0 < b1) (hL : 0 ≤ L)
    (hD : ∀ j : ℕ, D.p j = P.real {ω | X.cumDemand (X.count L ω) ω = j})
    (Q : ℕ) (hQ : 0 < Q) (R : ℤ)
    (hR : ∀ y : ℤ, windowCost D h b1 Q R ≤ windowCost D h b1 Q y) (y0 : ℤ)
    (m : ℕ → Ω → ℕ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ T in Filter.atTop, windowCost D h b1 Q R / Q - ε ≤ avgCost X D h b1 L Q y0 m T ω := by sorry

end InventoryControl
