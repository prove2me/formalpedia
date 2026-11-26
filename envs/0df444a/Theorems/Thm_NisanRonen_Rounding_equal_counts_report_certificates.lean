-- Prove2me | Theorems.Thm_NisanRonen_Rounding_equal_counts_report_certificates
-- name    : NisanRonen.Rounding.equal_counts_report_certificates
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:57:27.51624+00:00
-- url     : https://prove2.me/theorems/d0424db3-bf04-5181-817d-08760f9f8f38
-- title:
--   Fixed allocation priority gives report certificates for equal numbers of jobs and machines
-- statement:
--   For at least three machines and an equal number of jobs, any exact rounded solver with fixed injective allocation priority satisfies the report-certificate criterion at this job count if twice the rounding mesh is at most εa. The bound holds for arbitrary bounded processing times and declaration-optimal reports, for every comparator allocation.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9, https://doi.org/10.1006/game.1999.0790. Equal numbers of jobs and machines in the report-certificate reduction.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem equal_counts_report_certificates {n : ℕ} [NeZero n] {a b δ ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) (hδε : 2 * δ ≤ ε * a) (hn : 3 ≤ n)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin n → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin n → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin n → Fin n,
        roundedMakespan δ y (corrStar y v) =
          roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin n → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i))
    (y : Fin n → Fin n) :
    HasAllocationCertificates f δ a b t d ((1 + ε) * makespan y (corrStar y t)) := by sorry

end NisanRonen.Rounding
