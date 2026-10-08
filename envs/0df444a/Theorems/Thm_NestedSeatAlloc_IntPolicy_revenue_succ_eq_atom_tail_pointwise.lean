-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_succ_eq_atom_tail_pointwise
-- name    : NestedSeatAlloc.IntPolicy.revenue_succ_eq_atom_tail_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:04:56.135293+00:00
-- url     : https://prove2.me/theorems/91761832-1585-4477-962b-04ef40ea9027
-- title:
--   Pointwise finite-atom and strict-tail partition of recursive revenue
-- statement:
--   For integer-valued next demand and a seat count in the closed unit interval above an integer protection level, next-level recursive revenue equals the sum over demand atoms up to n plus the common strict-tail payoff. The endpoint case demand=n+1 and residual seats=n+1 is assigned to the tail by exact equality of the two recursive branches.
-- source:
--   A pointwise source-faithful component of the Open theorem NestedSeatAlloc.IntPolicy.clbi_next_demand_atom_tail_expectation (UUID 4d6786ca-689f-452c-8268-ee26d45fe3f2). It partitions the recursive k+1 revenue according to the integer witness d for X(k+1): d≤n selects exactly one finite atom; d>n gives the strict-tail expression. At the closed right endpoint, d=n+1 and s-p(k)=n+1, the recursion's final branch equals the tail payoff because s-d=p(k). This helper handles no integration or independence claim; those remain in the parent theorem.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open Classical

namespace NestedSeatAlloc.IntPolicy

open Classical

theorem revenue_succ_eq_atom_tail_pointwise
    {Ω : Type*} (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hint : ∀ i ω, ∃ d : ℕ, X i ω = d)
    (k n : ℕ) (hk : 0 < k) (p : ℕ → ℕ) (s : ℝ)
    (hs : s ∈ Set.Icc ((p k : ℝ) + n) ((p k : ℝ) + n + 1)) :
    ∀ ω,
      revenue f (fun j => (p j : ℝ)) (fun i => X i ω) (k + 1) s =
        (∑ i ∈ Finset.range (n + 1),
          (if X (k + 1) ω = (i : ℝ) then (i : ℝ) * f (k + 1) +
            revenue f (fun j => (p j : ℝ)) (fun i => X i ω) k (s - i)
           else 0)) +
        (if (n : ℝ) < X (k + 1) ω then
          (s - (p k : ℝ)) * f (k + 1) +
            revenue f (fun j => (p j : ℝ)) (fun i => X i ω) k (p k : ℝ)
         else 0) := by sorry

end NestedSeatAlloc.IntPolicy
