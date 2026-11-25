-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_polynomialCertificate
-- name    : OptimalAffinity.oa2x2_polynomialCertificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:56:42.202256+00:00
-- url     : https://prove2.me/theorems/5c6d91eb-d37b-4e1a-a3a1-baee078e9377
-- title:
--   Optimal Affinity: oa2x2 polynomial Certificate
-- statement:
--   The Optimal Affinity construction uses the oa2x2 polynomial Certificate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/GlobalMaximum.lean#L9-L14
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/GlobalMaximum.lean#L9-L14

module
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_polynomialCertificate (x y : ℝ) :
    12 * (3 * x - 2 * y - 7 * y ^ 2 + 6 * x ^ 2 * y) =
      (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) +
      (3 * x - 2 * y - 1) *
        (4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12) := by sorry
