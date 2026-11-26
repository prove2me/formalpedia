-- Prove2me | Theorems.Thm_NisanRonen_Rounding_bundle_report_bound_with_reserved_machine
-- name    : NisanRonen.Rounding.bundle_report_bound_with_reserved_machine
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:36:40.901794+00:00
-- url     : https://prove2.me/theorems/60d5765b-fc64-4263-936c-6d19759bc4a3
-- title:
--   A reserved machine detects an overreported bundle
-- statement:
--   Fix a rounded threshold in the declaration box and a machine whose report passes the unilateral optimality test. Suppose a bundle has true rounded load strictly below the threshold and its declared load fits after one task is removed. If the other tasks can be placed below the threshold using the minimum processing time and avoiding the tested machine and one reserved machine, then the full bundle’s declared rounded load is at most the threshold.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9, https://doi.org/10.1006/game.1999.0790. A necessary bundle condition for the unilateral declaration optimality test.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem bundle_report_bound_with_reserved_machine {n k : ℕ} [NeZero n] {a b δ m : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hma : a ≤ m) (hmb : m ≤ b) (hmround : roundUp δ m = m)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (i spare : Fin n) (hspare : spare ≠ i)
    (t r : Fin k → ℝ) (ht : ∀ j, a ≤ t j ∧ t j ≤ b) (hr : ∀ j, a ≤ r j ∧ r j ≤ b)
    (hop : DeclarationOptimal f δ a b i t r)
    (S : Finset (Fin k)) (j₀ : Fin k) (hj₀ : j₀ ∈ S)
    (bg : Fin k → Fin n) (hbg : ∀ j (_ : j ∉ S), bg j ≠ i ∧ bg j ≠ spare)
    (hbgload : ∀ l : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j => j ∉ S ∧ bg j = l), roundUp δ a) < m)
    (htload : (∑ j ∈ S, roundUp δ (t j)) < m)
    (hrErase : (∑ j ∈ S.erase j₀, roundUp δ (r j)) ≤ m) :
    (∑ j ∈ S, roundUp δ (r j)) ≤ m := by sorry

end NisanRonen.Rounding
