-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_weighted_atom_tail_affine
-- name    : NestedSeatAlloc.IntPolicy.clbi_weighted_atom_tail_affine
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T04:02:58.603394+00:00
-- url     : https://prove2.me/theorems/3e0c3146-d188-4023-8b5a-9c6f8731cd51
-- title:
--   Affine assembly for finite integer-demand atoms and the tail
-- statement:
--   If every shifted lower-level revenue term is affine on the translated unit interval, then any finite weighted sum of the integer-demand atom payoffs together with the strict-tail payoff is affine on the original unit interval.
-- source:
--   Source-faithful affine assembly step for NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation_pos (8e1ee4c8-6861-40fa-8d3b-46e943c721f1) at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. On each atom i, the induction hypothesis supplies g(s-i)=A_i+B_i(s-i); distributing the finite weighted sum collects an intercept and slope, while the strict-tail term is affine with slope c. The positive-index parent separately proves the atom/tail expectation identity using next-demand independence.

import Mathlib

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem clbi_weighted_atom_tail_affine
    (n m : ℕ) (c a tailWeight tailRevenue : ℝ)
    (w : ℕ → ℝ) (g H : ℝ → ℝ)
    (hunit : ∀ i : ℕ, i ≤ n → ∃ ai bi : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        g (s - i) = ai + bi * (s - i))
    (hexpect : ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
      H s = (∑ i ∈ Finset.range (n + 1),
        w i * ((i : ℝ) * c + g (s - i))) +
        tailWeight * ((s - a) * c + tailRevenue)) :
    ∃ A B : ℝ, ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1), H s = A + B * s := by sorry

end NestedSeatAlloc.IntPolicy
