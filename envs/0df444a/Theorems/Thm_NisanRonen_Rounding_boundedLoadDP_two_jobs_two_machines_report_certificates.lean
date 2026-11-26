-- Prove2me | Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_two_jobs_two_machines_report_certificates
-- name    : NisanRonen.Rounding.boundedLoadDP_two_jobs_two_machines_report_certificates
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:14:47.632491+00:00
-- url     : https://prove2.me/theorems/1e61bd36-5a5f-5fac-ac0d-12e3a6317bcd
-- title:
--   The bounded load dynamic program supplies report certificates for two jobs and two machines
-- statement:
--   For two machines and two jobs, the colexicographic bounded load dynamic program satisfies the report-certificate criterion on the full bounded box, provided δ < a and 2δ ≤ εa. This includes all declaration-optimal profiles and all comparator allocations.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9, https://doi.org/10.1006/game.1999.0790. The two-job two-machine case of the report-certificate reduction.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion
import Definitions.Def_NisanRonen_Rounding_boundedLoadDP

namespace NisanRonen.Rounding

theorem boundedLoadDP_two_jobs_two_machines_report_certificates {a b δ ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (hδa : δ < a) (hstep : 2 * δ ≤ ε * a)
    (t d : Fin 2 → Fin 2 → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal (boundedLoadDP (n := 2) (⌈b / δ⌉.toNat)) δ a b i (t i) (d i))
    (y : Fin 2 → Fin 2) :
    HasAllocationCertificates (boundedLoadDP (n := 2) (⌈b / δ⌉.toNat)) δ a b t d
      ((1 + ε) * makespan y (corrStar y t)) := by sorry

end NisanRonen.Rounding
