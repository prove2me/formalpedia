-- Prove2me | Theorems.Thm_InventoryControl_serial_pot_lower_bound
-- name    : InventoryControl.serial_pot_lower_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:12:31.158221+00:00
-- url     : https://prove2.me/theorems/845ea79a-0369-411e-b0d5-5b9e8a6a57b8
-- title:
--   Eq. (9.16) implies Eq. (9.18): the relaxed optimum is a lower bound for every powers-of-two policy
-- statement:
--   Let $Q^{\mathrm{rel}}$ minimize the serial cost (9.17) over positive batch quantities
--   satisfying the relaxed constraints (9.18). Then every family of positive batch quantities
--   satisfying Roundy's constraints (9.16), $Q_i = 2^{k_i}Q_{i-1}$ with $k_i \ge 0$, also satisfies
--   (9.18), and its cost is at least the relaxed optimum:
--
--   $$ Q_{i-1} \le Q_i \ \text{ for all } i, \qquad\text{and}\qquad
--      \sum_{i}\Big(e_i\frac{Q_i}{2} + A_i\frac{d}{Q_i}\Big) \;\ge\;
--      \sum_{i}\Big(e_i\frac{Q^{\mathrm{rel}}_i}{2} + A_i\frac{d}{Q^{\mathrm{rel}}_i}\Big). $$
--
--   This is the easy direction of Roundy's argument, and it is the sense in which the relaxed
--   optimum is "a lower bound for the costs when using the constraints (9.16)". The book goes on
--   to argue that the same value bounds the cost of any policy at all, including ones whose batch
--   quantities vary over time; that stronger claim, which needs a model of time-varying policies,
--   is not formalized in this mission.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 179, Sect. 9.2.2: 'Note that (9.16) implies (9.18) while the opposite is not true. Therefore, by using (9.18) we will get a lower bound for the costs when using the constraints (9.16)'

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem serial_pot_lower_bound {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (Qrel : Fin N → ℝ)
    (hopt : ∀ Q : Fin N → ℝ, (∀ i, 0 < Q i) → SerialNested Q →
      serialCost A e d Qrel ≤ serialCost A e d Q)
    (Q : Fin N → ℝ) (hpos : ∀ i, 0 < Q i) (hpot : SerialPowerOfTwo Q) :
    SerialNested Q ∧ serialCost A e d Qrel ≤ serialCost A e d Q := by sorry

end InventoryControl
