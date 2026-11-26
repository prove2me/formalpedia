-- Prove2me | Theorems.Thm_NisanRonen_Rounding_two_jobs_grid_bound_split_choice
-- name    : NisanRonen.Rounding.two_jobs_grid_bound_split_choice
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:25:13.629818+00:00
-- url     : https://prove2.me/theorems/081a09e9-3641-4e34-98df-e46c5986fdd6
-- title:
--   Grid makespan bound when the colexicographic choice assigns the jobs to different machines
-- statement:
--   Two machines and two jobs give four allocations, ordered colexicographically. Suppose every rounded report is declaration-optimal against all integer opponent rows in the box. If the selected allocation assigns the jobs to different machines, its true rounded makespan is no more than one grid unit above any comparator’s.
-- source:
--   Integer comparisons for the two-job two-machine case of the report-certificate reduction for Nisan–Ronen Theorem 5.9.

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

namespace NisanRonen.Rounding

theorem two_jobs_grid_bound_split_choice (a b p q r s P Q R S : ℤ) :
    let score := fun (p q r s : ℤ) => (![p + q, max q r, max p s, r + s] : Fin 4 → ℤ)
    let preferred := fun (cost : Fin 4 → ℤ) (i : Fin 4) =>
      ∀ j, cost i ≤ cost j ∧ (j < i → cost i < cost j)
    let stable := fun (report truth : Fin 4 → ℤ) =>
      ∀ i, preferred report i → ∀ j, truth i ≤ truth j
    let inBox := fun v : ℤ => a ≤ v ∧ v ≤ b
    2 ≤ a →
    inBox p → inBox q → inBox r → inBox s →
    inBox P → inBox Q → inBox R → inBox S →
    (∀ w u, inBox w → inBox u → stable (score P Q w u) (score p q w u)) →
    (∀ w u, inBox w → inBox u → stable (score w u R S) (score w u r s)) →
    ∀ i j : Fin 4, (i = 1 ∨ i = 2) →
      preferred (score P Q R S) i → score p q r s i ≤ score p q r s j + 1 := by sorry

end NisanRonen.Rounding
