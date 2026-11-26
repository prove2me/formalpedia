-- Prove2me | Theorems.Thm_NisanRonen_Rounding_priority_certificates_of_true_load_bound
-- name    : NisanRonen.Rounding.priority_certificates_of_true_load_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:45:59.843506+00:00
-- url     : https://prove2.me/theorems/2485dfe0-815e-4a7f-b8be-00be7a2815dc
-- title:
--   Fixed allocation priority supplies execution certificates from a true load bound
-- statement:
--   Fix an exact rounded solver that breaks ties by a single strict priority order on allocations. Suppose the selected allocation has rounded true makespan at most a grid threshold. For each machine, assume its declared rounded load is at most the larger of that threshold and the rounded upper bound on one job, or every other machine’s declared load is at most the threshold. Then the selected allocation has report certificates for every occupied machine at the grid threshold.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9, https://doi.org/10.1006/game.1999.0790. An allocation preservation result for the report-certificate criterion.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem priority_certificates_of_true_load_bound {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin n,
        roundedMakespan δ y (corrStar y v) =
          roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b) (m : ℤ)
    (htrue : roundedMakespan δ (allocOf f δ d) (corrStar (allocOf f δ d) t) ≤ δ * (m : ℝ))
    (hload : ∀ i : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j => allocOf f δ d j = i), roundUp δ (d i j)) ≤
        max (δ * (m : ℝ)) (roundUp δ b) ∨
      ∀ l ≠ i,
        (∑ j ∈ Finset.univ.filter (fun j => allocOf f δ d j = l), roundUp δ (d l j)) ≤ δ * (m : ℝ)) :
    HasAllocationCertificates f δ a b t d (δ * (m : ℝ)) := by sorry

end NisanRonen.Rounding
