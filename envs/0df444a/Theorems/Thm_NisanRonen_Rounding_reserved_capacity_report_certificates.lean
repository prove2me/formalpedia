-- Prove2me | Theorems.Thm_NisanRonen_Rounding_reserved_capacity_report_certificates
-- name    : NisanRonen.Rounding.reserved_capacity_report_certificates
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:01:44.813978+00:00
-- url     : https://prove2.me/theorems/e7e03436-ae8e-4838-ba31-e3d6acbb5ed9
-- title:
--   A reserved capacity bound supplies report certificates for arbitrary job counts
-- statement:
--   Suppose a grid threshold M lies in the declared interval and strictly exceeds a comparator’s true rounded makespan. If some integer c satisfies k−1 ≤ (n−2)c and c times the rounded minimum processing time is strictly below M, then every exact rounded solver has allocation certificates at M for in-box declaration-optimal profiles. There is no assumption on tie-breaking.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9, https://doi.org/10.1006/game.1999.0790. Capacity criterion for the report-certificate reduction.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem reserved_capacity_report_certificates {n k : ℕ} [NeZero n] {a b δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hMa : a ≤ M) (hMb : M ≤ b)
    (hgrid : roundUp δ M = M) (hn : 2 ≤ n)
    (c : ℕ) (hcount : k - 1 ≤ (n - 2) * c)
    (hspace : (c : ℝ) * roundUp δ a < M)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ l, DeclarationOptimal f δ a b l (t l) (d l))
    (y : Fin k → Fin n) (hy : roundedMakespan δ y (corrStar y t) < M) :
    HasAllocationCertificates f δ a b t d M := by sorry

end NisanRonen.Rounding
