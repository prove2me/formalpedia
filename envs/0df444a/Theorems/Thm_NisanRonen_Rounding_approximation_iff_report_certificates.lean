-- Prove2me | Theorems.Thm_NisanRonen_Rounding_approximation_iff_report_certificates
-- name    : NisanRonen.Rounding.approximation_iff_report_certificates
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:12:15.864855+00:00
-- url     : https://prove2.me/theorems/cf4f4534-26ab-4bd4-91ca-850fe27ba5ea
-- title:
--   Approximation across dominant strategies is equivalent to an allocation-only certificate criterion
-- statement:
--   For any exact rounded solver, the approximation bound across every profile of dominant strategies is equivalent to the certificate criterion on declarations and allocations. Each declaration is first tested by asking whether the allocation selected at every in-box profile stays optimal after truth-correcting that declaration. If all declarations pass, the criterion requires, for each occupied machine, a profile preserving its declaration and the allocation and admitting a schedule below the desired bound after truth correction.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, Definition 18, Definition 34, and Theorem 5.9, https://doi.org/10.1006/game.1999.0790. Reformulation of the implementation clause of the corrected Prove2Me statement.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion
import Definitions.Def_NisanRonen_Rounding_IsDominant

namespace NisanRonen.Rounding

theorem approximation_iff_report_certificates {n : ℕ} [NeZero n] {a b δ ε : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (hε : 0 ≤ ε)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b) :
    (∀ (k : ℕ) (t : Fin n → Fin k → ℝ), (∀ i j, a ≤ t i j ∧ t i j ≤ b) →
      ∀ s : Fin n → Strategy n k, (∀ i, IsDominant f δ a b i (t i) (s i)) →
      ∀ y : Fin k → Fin n,
        makespan (allocOf f δ (fun i => (s i).decl)) (actualTimes f δ s) ≤
          (1 + ε) * makespan y (corrStar y t)) ↔ CertificateCriterion f δ a b ε := by sorry

end NisanRonen.Rounding
