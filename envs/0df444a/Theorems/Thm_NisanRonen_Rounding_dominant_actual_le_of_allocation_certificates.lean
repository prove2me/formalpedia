-- Prove2me | Theorems.Thm_NisanRonen_Rounding_dominant_actual_le_of_allocation_certificates
-- name    : NisanRonen.Rounding.dominant_actual_le_of_allocation_certificates
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:41:41.293975+00:00
-- url     : https://prove2.me/theorems/f3d145a2-aab1-4903-a8f7-dda7f76b8eae
-- title:
--   Dominant execution bounds from declarations preserving the allocation
-- statement:
--   Let an exact rounded solver choose allocation $x$ at a profile of dominant strategies. Fix a real bound $C$. For each machine $i$, suppose there exists an in-box declaration matrix that agrees with $i$’s chosen declaration, induces the same allocation $x$, and admits a schedule with rounded makespan at most $C$ after replacing $i$’s declaration by its true row. Then the makespan of $x$ at the original profile’s actual execution times is at most $C$. A different comparison declaration matrix and schedule may be used for each machine.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9, p. 193, https://doi.org/10.1006/game.1999.0790. A sufficient condition for the implementation clause using Definition 18 and the corrected characterization of dominant strategies.

import Definitions.Def_NisanRonen_Rounding_IsDominant
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace NisanRonen.Rounding

theorem dominant_actual_le_of_allocation_certificates {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b)
    (s : Fin n → Strategy n k) (hs : ∀ i, IsDominant f δ a b i (t i) (s i))
    (C : ℝ)
    (hC : ∀ i : Fin n, ∃ d : Fin n → Fin k → ℝ,
      (∀ l j, a ≤ d l j ∧ d l j ≤ b) ∧ d i = (s i).decl ∧
      allocOf f δ d = allocOf f δ (fun l => (s l).decl) ∧
      ∃ y : Fin k → Fin n,
        roundedMakespan δ y (corrStar y (Function.update d i (t i))) ≤ C) :
    makespan (allocOf f δ (fun l => (s l).decl)) (actualTimes f δ s) ≤ C := by sorry

end NisanRonen.Rounding
