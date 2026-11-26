-- Prove2me | Theorems.Thm_NisanRonen_Rounding_allocation_certificates_with_spare_machine_or_trivial_instance
-- name    : NisanRonen.Rounding.allocation_certificates_with_spare_machine_or_trivial_instance
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:23:38.668307+00:00
-- url     : https://prove2.me/theorems/52946223-bcfa-581a-8cbe-fa65d022ebb1
-- title:
--   Report certificates when machines outnumber jobs or an instance has one machine or task
-- statement:
--   Use a grid spacing at most half the target error times the positive lower bound on processing times. The report certificate condition holds for every exact rounded solver on instances with more machines than tasks, one machine, or at most one task. Every declaration must satisfy the unilateral optimality test. The result applies to the prescribed compensation and rounded bonus with arbitrary tie-breaking.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6 and Theorem 5.9, https://doi.org/10.1006/game.1999.0790. A special case of the corrected implementation clause.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem allocation_certificates_with_spare_machine_or_trivial_instance {n k : ℕ} [NeZero n] {a b δ ε : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hstep : 2 * δ ≤ ε * a) (hsmall : n = 1 ∨ k ≤ 1 ∨ k < n)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t d : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b)
    (hd : ∀ i j, a ≤ d i j ∧ d i j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i)) (y : Fin k → Fin n) :
    HasAllocationCertificates f δ a b t d ((1 + ε) * makespan y (corrStar y t)) := by sorry

end NisanRonen.Rounding
