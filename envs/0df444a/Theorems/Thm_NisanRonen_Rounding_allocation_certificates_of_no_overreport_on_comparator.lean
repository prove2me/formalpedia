-- Prove2me | Theorems.Thm_NisanRonen_Rounding_allocation_certificates_of_no_overreport_on_comparator
-- name    : NisanRonen.Rounding.allocation_certificates_of_no_overreport_on_comparator
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:17:20.872538+00:00
-- url     : https://prove2.me/theorems/5a966b63-047a-4266-ac1e-e70bfad5c39e
-- title:
--   Comparison schedules without rounded overreports admit report certificates
-- statement:
--   Suppose the grid spacing is at most the target error times the positive lower bound on processing times. Fix a comparison schedule. If the rounded declaration on every machine-task pair used by this comparison schedule is at most the corresponding rounded true time, the original report matrix itself supplies the approximation certificate for every occupied machine. The condition is required only on pairs used by the comparison schedule.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, pp. 192–193, https://doi.org/10.1006/game.1999.0790. A sufficient condition for the report certificate criterion using the rounded makespan bound.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem allocation_certificates_of_no_overreport_on_comparator {n k : ℕ} [NeZero n] {a b δ ε : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hstep : δ ≤ ε * a) (f : List (Fin n → ℕ) → List (Fin n))
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ i j, a ≤ t i j) (hd : ∀ i j, a ≤ d i j ∧ d i j ≤ b)
    (y : Fin k → Fin n) (hy : ∀ j, roundUp δ (d (y j) j) ≤ roundUp δ (t (y j) j)) :
    HasAllocationCertificates f δ a b t d ((1 + ε) * makespan y (corrStar y t)) := by sorry

end NisanRonen.Rounding
