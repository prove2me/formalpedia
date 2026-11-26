-- Prove2me | Theorems.Thm_NisanRonen_Rounding_two_machine_execution_certificates_from_true_load
-- name    : NisanRonen.Rounding.two_machine_execution_certificates_from_true_load
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:41:26.193599+00:00
-- url     : https://prove2.me/theorems/0008b903-d522-504f-af23-3bb2a48654a2
-- title:
--   Two machines admit report certificates within the rounding factor of the selected true cost
-- statement:
--   For any number of jobs on two machines, any fixed-priority exact rounded solver and declaration-optimal profile admit allocation certificates at (1+δ/a) times the selected allocation’s true rounded makespan. The statement bounds execution for a given allocation and imposes no condition on the reported loads.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9. The execution part of the report-certificate reduction for two machines.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

namespace NisanRonen.Rounding

theorem two_machine_execution_certificates_from_true_load {k : ℕ} {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin 2 → ℕ) → List (Fin 2)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin 2) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin 2 → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin 2, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin 2 → Fin k → ℝ) (ht : ∀ l j, a ≤ t l j)
    (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i)) :
    let x := allocOf f δ d
    HasAllocationCertificates f δ a b t d
      ((1 + δ / a) * roundedMakespan δ x (corrStar x t)) := by sorry

end NisanRonen.Rounding
