-- Prove2me | Theorems.Thm_InventoryControl_serial_aggregation
-- name    : InventoryControl.serial_aggregation
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:12:03.221451+00:00
-- url     : https://prove2.me/theorems/a43ad602-d14f-4b64-8619-4ebc9f2ab89b
-- title:
--   Sect. 9.2.2, pp. 180-181: if $A_i/e_i < A_{i-1}/e_{i-1}$ then $Q_i = Q_{i-1}$ in the relaxed optimum
-- statement:
--   Let $Q^{\mathrm{rel}}$ be an optimal solution of the relaxed serial problem, minimizing the
--   cost (9.17) over positive batch quantities with $Q_{i-1} \le Q_i$, for $d, A_i, e_i > 0$. If
--   for two consecutive stages
--
--   $$ \frac{A_i}{e_i} \;<\; \frac{A_{i-1}}{e_{i-1}}, $$
--
--   equivalently if the unconstrained optima satisfy $Q^{*}_i < Q^{*}_{i-1}$, then the
--   constraint between them is tight: $Q^{\mathrm{rel}}_i = Q^{\mathrm{rel}}_{i-1}$.
--
--   The book's argument is by contradiction from convexity: if $Q_i > Q_{i-1}$ in the optimum,
--   then $Q_i \le Q^{*}_i$ (otherwise reducing $Q_i$ would lower the cost while keeping the
--   constraints) and $Q_{i-1} \ge Q^{*}_{i-1}$, so $Q_i \le Q^{*}_i < Q^{*}_{i-1} \le Q_{i-1}$.
--   It is the justification of the aggregation algorithm: two such stages are merged into one
--   with ordering cost $A_{i-1} + A_i$ and echelon holding cost $e_{i-1} + e_i$, and the relaxed
--   optimum is found by repeating this until the ratios $A_i/e_i$ are nondecreasing and applying
--   the EOQ formula to each aggregate.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, pp. 180-181, Sect. 9.2.2: 'Assume that for some i, Ai/ei < Ai-1/ei-1 ... Consequently, Qi = Qi-1 in the optimal solution of the relaxed problem'

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem serial_aggregation {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (hd : 0 < d)
    (hA : ∀ i, 0 < A i) (he : ∀ i, 0 < e i) (Qrel : Fin N → ℝ) (hpos : ∀ i, 0 < Qrel i)
    (hnest : SerialNested Qrel)
    (hopt : ∀ Q : Fin N → ℝ, (∀ i, 0 < Q i) → SerialNested Q →
      serialCost A e d Qrel ≤ serialCost A e d Q)
    (i j : Fin N) (hij : j.val = i.val + 1) (hratio : A j / e j < A i / e i) :
    Qrel j = Qrel i := by sorry

end InventoryControl
