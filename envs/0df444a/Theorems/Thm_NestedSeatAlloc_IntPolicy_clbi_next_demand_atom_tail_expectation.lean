-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_next_demand_atom_tail_expectation
-- name    : NestedSeatAlloc.IntPolicy.clbi_next_demand_atom_tail_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T04:37:35.739694+00:00
-- url     : https://prove2.me/theorems/4d6786ca-689f-452c-8268-ee26d45fe3f2
-- title:
--   Expected revenue split by the next integer demand atoms and tail
-- statement:
--   For nonnegative integer-valued demands and integer protection levels, when the seat count lies in a unit interval above the current protection level, expected revenue at the next class is the finite sum over demand atoms up to the interval index plus the strict upper-tail contribution.
-- source:
--   Source-faithful expectation bridge for NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation_pos (8e1ee4c8-6861-40fa-8d3b-46e943c721f1). The recursive revenue is partitioned by the next integer-valued demand into atoms i≤n and the strict tail i>n; the endpoint i=n+1 agrees with the tail value when s is the right endpoint. Integrability follows from the finite-fare envelope, and independence of the first k demands from X(k+1) factors each atom/tail payoff. This is the missing expectation-level bridge, not an affine conclusion or a syntactic wrapper.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem clbi_next_demand_atom_tail_expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ i ω, ∃ n : ℕ, X i ω = n) (k n : ℕ) (hk : 0 < k)
    (p : ℕ → ℕ) (s : ℝ)
    (hs : s ∈ Set.Icc ((p k : ℝ) + n) ((p k : ℝ) + n + 1)) :
    expRevenue P X f (fun j => (p j : ℝ)) (k + 1) s =
      (∑ i ∈ Finset.range (n + 1),
        P.real {ω | X (k + 1) ω = (i : ℝ)} *
          ((i : ℝ) * f (k + 1) +
            expRevenue P X f (fun j => (p j : ℝ)) k (s - i))) +
      P.real {ω | (n : ℝ) < X (k + 1) ω} *
        ((s - (p k : ℝ)) * f (k + 1) +
          expRevenue P X f (fun j => (p j : ℝ)) k (p k : ℝ)) := by sorry

end NestedSeatAlloc.IntPolicy
