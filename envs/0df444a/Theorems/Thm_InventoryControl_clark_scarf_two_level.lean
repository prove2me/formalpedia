-- Prove2me | Theorems.Thm_InventoryControl_clark_scarf_two_level
-- name    : InventoryControl.clark_scarf_two_level
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:22:56.31868+00:00
-- url     : https://prove2.me/theorems/f61e16d7-d6ab-4edd-8d8f-00808fcf5c0f
-- title:
--   Sect. 10.1.1: the Clark-Scarf decomposition — echelon order-up-to levels $(S_1, S_2)$ minimize the expected period cost of the two-level serial system
-- statement:
--   The Clark-Scarf decomposition for a two-level serial system, the central result of
--   Chapter 10.
--
--   Installation 1 faces normally distributed period demand (mean $\mu$, standard deviation
--   $\sigma > 0$, independent across periods) and replenishes from installation 2, which
--   replenishes from an outside supplier with infinite supply; lead-times are $L_1$ and $L_2$
--   periods, demand is backordered, and costs are echelon holding costs $e_1, e_2 \ge 0$ and a
--   shortage cost $b_1 > 0$ per unit and period, with $h_1 = e_1 + e_2$ and $h_2 = e_2$. In an
--   arbitrary period the total expected cost is determined by the echelon position $y_2$ chosen
--   at installation 2 and the realized position $y_1$ at installation 1 a lead-time later, which
--   is subject to $y_1 \le y_2 - D(L_2)$ and may depend on $D(L_2)$; after the reallocation
--   (10.4)-(10.5) it is $\mathbb{E}\big[\tilde C_2(y_2) + \tilde C_1(y_1)\big]$.
--
--   Let $S_1$ be the newsboy level of Eq. (10.8),
--   $\Phi\big((S_1 - \mu_1'')/\sigma_1''\big) = (e_2 + b_1)/(h_1 + b_1)$, and let $S_2$ minimize
--   the total cost $\hat C_2$ of Eq. (10.9). Then:
--
--   1. for every $y_2$ and every allocation rule $u \mapsto a(u)$ with $a(u) \le y_2 - u$ (and
--      finite expected cost),
--      $$ \hat C_2(S_2) \;\le\; \mathbb{E}\big[\tilde C_2(y_2) + \tilde C_1\big(a(D(L_2))\big)\big]; $$
--   2. the echelon order-up-to policy $(S_1, S_2)$, which sets $y_2 = S_2$ and
--      $y_1 = \min\{S_1, S_2 - D(L_2)\}$, attains $\hat C_2(S_2)$.
--
--   In words: the optimal policy is an echelon-stock order-up-to policy at both installations,
--   $S_1$ is found from a newsboy problem that does not involve installation 2 at all, and $S_2$ is
--   then found by minimizing a convex function of one variable in which installation 2's
--   inability to deliver appears as an induced shortage cost. This is the decomposition Clark and
--   Scarf discovered, and the origin of the echelon-inventory measure. In Example 10.1
--   ($L_1 = L_2 = 5$, $\mu = 10$, $\sigma = 5$, $e_1 = 0.5$, $e_2 = 1$, $b_1 = 10$) it gives
--   $S_1 = 81.0$ and $S_2 = 129.7$ with total cost $39.4$.
--
--   **Formalization Note** The theorem is the per-period decomposition the book derives; it does
--   not model the infinite-horizon dynamics, in which the same stationary policy is applied in
--   every period and is feasible because the outside supplier has infinite supply (the book's
--   "obvious" step). Allocation rules are arbitrary functions of the realized lead-time demand
--   with an explicit integrability hypothesis, since a rule with infinite expected cost is not a
--   competitor. $S_1$ and $S_2$ are characterized rather than constructed; their existence for
--   $e_1 > 0$ is established by the other items of this mission.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, pp. 193-196, Sect. 10.1.1 'Serial System', Eq. (10.1)-(10.9) and the conclusions on p. 196: 'this optimal policy can be realized if we apply an (echelon stock) order-up-to-S policy with Se1 = y-hat*1' and 'it is optimal to apply an echelon stock order-up-to-S policy with Se2 = y*2'; after Clark and Scarf (1960) and Federgruen and Zipkin (1984)

import Definitions.Def_InventoryControl_clarkScarf

namespace InventoryControl

theorem clark_scarf_two_level (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 L2 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (S2 : ℝ) (hS2 : ∀ y2 : ℝ, csTotalCost e1 e2 b1 mu sigma L1 L2 S1 S2
      ≤ csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y2) :
    (∀ y2 : ℝ, ∀ a : ℝ → ℝ, (∀ u, a u ≤ y2 - u) →
        MeasureTheory.Integrable (fun u => csStage1Cost e1 e2 b1 mu sigma L1 (a u))
          (csDemand mu sigma L2) →
        csTotalCost e1 e2 b1 mu sigma L1 L2 S1 S2
          ≤ ∫ u, (csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 (a u))
              ∂(csDemand mu sigma L2))
      ∧ csTotalCost e1 e2 b1 mu sigma L1 L2 S1 S2
          = ∫ u, (csStage2Cost e2 mu L2 S2 + csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (S2 - u)))
              ∂(csDemand mu sigma L2) := by sorry

end InventoryControl
