-- Prove2me | Theorems.Thm_NisanRonen_Rounding_strict_reported_bottleneck_execution_certificate
-- name    : NisanRonen.Rounding.strict_reported_bottleneck_execution_certificate
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:32:11.987182+00:00
-- url     : https://prove2.me/theorems/10cd8488-c929-4c99-924c-42c13f9bef1e
-- title:
--   A strict reported bottleneck admits an execution certificate under fixed priority
-- statement:
--   Fix an exact rounded solver with a report-independent injective priority on allocations. Suppose its selected allocation has true rounded makespan at most a grid threshold. If a focal declaration is declaration-optimal and its selected reported load strictly exceeds both the threshold and every other reported load, there is a report profile preserving the focal declaration and the allocation at which focal truth correction has rounded makespan at most the threshold.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9. A sufficient condition for the report-certificate reduction.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem strict_reported_bottleneck_execution_certificate {n k : ℕ} [NeZero n] {a b δ : ℝ} (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin n, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (i : Fin n) (hop : DeclarationOptimal f δ a b i (t i) (d i)) (m : ℤ) :
    let x := allocOf f δ d
    roundedMakespan δ x (corrStar x t) ≤ δ * (m : ℝ) →
    δ * (m : ℝ) < (∑ j ∈ Finset.univ.filter (fun j => x j = i), roundUp δ (d i j)) →
    (∀ l ≠ i, (∑ j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ (d l j)) <
      ∑ j ∈ Finset.univ.filter (fun j => x j = i), roundUp δ (d i j)) →
    ∃ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) ∧
      v i = d i ∧ allocOf f δ v = x ∧
      roundedMakespan δ x (corrStar x (Function.update v i (t i))) ≤ δ * (m : ℝ) := by sorry

end NisanRonen.Rounding
