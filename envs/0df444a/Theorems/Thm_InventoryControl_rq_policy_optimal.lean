-- Prove2me | Theorems.Thm_InventoryControl_rq_policy_optimal
-- name    : InventoryControl.rq_policy_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:06:00.48255+00:00
-- url     : https://prove2.me/theorems/8c57b21c-4df1-4d78-8a45-1139db56121a
-- title:
--   Proposition 6.1: an $(R,Q)$ policy is optimal when ordering in batches
-- statement:
--   Proposition 6.1 of Axsäter, *Inventory Control*: **an $(R,Q)$ policy is optimal.**
--
--   The setting is Sect. 6.2.1. Demand is compound Poisson: customers arrive at rate $\lambda$
--   and each demands an integral number of units, i.i.d., not all demands being multiples of some
--   integer larger than one. The lead-time $L$ is constant, and $D(L)$, the demand over a
--   lead-time, has the law $D$. A holding cost $h > 0$ and a shortage cost $b_1 > 0$ per unit and
--   time unit are charged; there are no ordering costs, but all orders must be multiples of a
--   given batch quantity $Q \ge 1$ and can only be triggered by customer demands. For an inventory
--   position $k$ the expected holding-plus-shortage cost rate a lead-time later is
--   $g(k) = -b_1(k - \mu') + (h+b_1)\sum_{j=1}^{k} j\Pr[D(L) = k-j]$, so the cost rate at time
--   $t + L$ is $g(y_t)$, where $y_t$ is the position at time $t$. Let
--   $\bar g(y) = \sum_{j=1}^{Q} g(y + j)$ and let $R$ be an integer minimizing $\bar g$.
--
--   The claim has two parts, both almost sure:
--
--   1. for every ordering rule $m$ and every initial position $y_0$,
--      $$ \liminf_{T\to\infty} \frac{1}{T}\int_0^T g\big(y^{m}_{t-L}\big)\,\mathrm{d}t \;\ge\; \frac{\bar g(R)}{Q}; $$
--   2. the $(R,Q)$ policy with this $R$ attains it:
--      $$ \frac{1}{T}\int_0^T g\big(y^{(R,Q)}_{t-L}\big)\,\mathrm{d}t \;\longrightarrow\; \frac{\bar g(R)}{Q}. $$
--
--   Together: no policy that orders in batches of $Q$ can do better in the long run than the
--   $(R,Q)$ policy whose reorder point minimizes $\bar g$. The book notes that for $Q = 1$ this
--   is the optimality of an $S$ policy when there are no ordering costs, and that for continuous
--   or Poisson demand it also gives the optimality of $(s,S)$ policies, which coincide with
--   $(R,Q)$ policies there.
--
--   **Formalization Note** A policy is any function assigning to each demand epoch and outcome a
--   number of batches; no measurability is required, since the lower bound is pathwise. The
--   average is over $[0, T]$ with the cost rate $g$ evaluated at the position a lead-time earlier,
--   the position being $y_0$ before time $0$; "$\liminf \ge c$" is stated as "for every
--   $\varepsilon > 0$, eventually $\ge c - \varepsilon$". The initial position is arbitrary, as in
--   the book, and the reorder point is any minimizer of $\bar g$, whose existence follows from
--   $g(k) \to \infty$ as $|k| \to \infty$ (a theorem of the previous mission).
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, pp. 113-115, Sect. 6.2.1 'Optimality of (R, Q) Policies When Ordering in Batches', Proposition 6.1 and its proof; after Chen (2000)

import Definitions.Def_InventoryControl_rqPolicy

namespace InventoryControl

theorem rq_policy_optimal {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (D : DiscreteDemand)
    (h b1 L : ℝ) (hh : 0 < h) (hb : 0 < b1) (hL : 0 ≤ L)
    (hD : ∀ j : ℕ, D.p j = P.real {ω | X.cumDemand (X.count L ω) ω = j})
    (Q : ℕ) (hQ : 0 < Q) (R : ℤ)
    (hR : ∀ y : ℤ, windowCost D h b1 Q R ≤ windowCost D h b1 Q y) (y0 : ℤ) :
    (∀ m : ℕ → Ω → ℕ, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ T in Filter.atTop, windowCost D h b1 Q R / Q - ε ≤ avgCost X D h b1 L Q y0 m T ω)
      ∧ (∀ᵐ ω ∂P, Filter.Tendsto (fun T => avgCost X D h b1 L Q y0 (rqOrders X R Q y0) T ω)
            Filter.atTop (nhds (windowCost D h b1 Q R / Q))) := by sorry

end InventoryControl
