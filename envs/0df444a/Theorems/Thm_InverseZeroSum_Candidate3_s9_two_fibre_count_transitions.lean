-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s9_two_fibre_count_transitions
-- name    : InverseZeroSum.Candidate3.s9_two_fibre_count_transitions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:39.670486+00:00
-- url     : https://prove2.me/theorems/5f07c2ff-fdb0-4e9c-b4e4-a1d57d65534c
-- title:
--   Candidate3: s9 two fibre count transitions
-- statement:
--   The elementary local cardinality obstruction behind the S040 transition list.
--   Here p,q are the two affected multiplicities before replacing one occurrence
--   of b by a; both residuals have at most two copies of each value and at most
--   one singleton value. This does not yet transport the property through a
--   certificate-level representative swap.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2677-L2682
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2677-L2682

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s9_two_fibre_count_transitions
    (p q : ℕ) (hp : p + 1 ≤ 2) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hBefore : p = 1 → q ≠ 1)
    (hAfter : p + 1 = 1 → q - 1 ≠ 1) :
    (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 2) := by sorry
