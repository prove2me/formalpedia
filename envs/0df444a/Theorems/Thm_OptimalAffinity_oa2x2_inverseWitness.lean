-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_inverseWitness
-- name    : OptimalAffinity.oa2x2_inverseWitness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:53:27.843063+00:00
-- url     : https://prove2.me/theorems/0d0c0e4c-94f9-5d09-a2b4-7f1885fea3ea
-- title:
--   Optimal Affinity: oa2x2 inverse Witness
-- statement:
--   The Optimal Affinity construction uses the oa2x2 inverse Witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L134-L139
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L134-L139

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_inverseWitness :
    (-1 : ℤ) * 1 + 2 * 1 = 1 ∧
    (-1 : ℤ) * 2 + 2 * 1 = 0 ∧
    (1 : ℤ) * 1 + (-1) * 1 = 0 ∧
    (1 : ℤ) * 2 + (-1) * 1 = 1 := by sorry
