-- Prove2me | Theorems.Thm_InventoryControl_serial_relaxed_min_exists
-- name    : InventoryControl.serial_relaxed_min_exists
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:11:26.603995+00:00
-- url     : https://prove2.me/theorems/65480728-491f-48a9-96ac-1ba2319dcb78
-- title:
--   The relaxed problem (9.17) subject to (9.18) has an optimal solution
-- statement:
--   For a serial system with $N$ stages, final demand $d > 0$, ordering costs $A_i > 0$ and
--   echelon holding costs $e_i > 0$, there are positive nested batch quantities
--   $Q^{\mathrm{rel}}_1 \le \dots \le Q^{\mathrm{rel}}_N$ that minimize the cost (9.17) over all
--   positive batch quantities satisfying the relaxed constraints (9.18).
--
--   The book speaks of "the unique solution of the relaxed problem" and computes it by
--   aggregation; that a minimum exists is presupposed. It does because each term
--   $e_iQ_i/2 + A_id/Q_i$ tends to infinity as $Q_i \to 0$ or $Q_i \to \infty$, so the search
--   can be confined to a compact box, on which the continuous objective attains its minimum, and
--   the constraint set is closed. Positivity of every $A_i$ and $e_i$ is needed: with $e_i = 0$
--   the cost decreases without bound as $Q_i \to \infty$, and with $A_i = 0$ as $Q_i \to 0$.
--
--   **Formalization Note** Uniqueness is not asserted here.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 179, Sect. 9.2.2: 'The objective function (9.17) is convex and the constraints (9.18) are linear. The unique solution of the relaxed problem can therefore be obtained through the Lagrangean relaxation'; existence is presupposed

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem serial_relaxed_min_exists {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (hd : 0 < d)
    (hA : ∀ i, 0 < A i) (he : ∀ i, 0 < e i) :
    ∃ Qrel : Fin N → ℝ, (∀ i, 0 < Qrel i) ∧ SerialNested Qrel ∧
      ∀ Q : Fin N → ℝ, (∀ i, 0 < Q i) → SerialNested Q →
        serialCost A e d Qrel ≤ serialCost A e d Q := by sorry

end InventoryControl
