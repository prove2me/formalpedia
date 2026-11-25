-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_literalStoichiometry
-- name    : OptimalAffinity.oa2x2_literalStoichiometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:53:30.837346+00:00
-- url     : https://prove2.me/theorems/9f715b7d-f672-410f-9e6e-86fde3413b0f
-- title:
--   Optimal Affinity: oa2x2 literal Stoichiometry
-- statement:
--   The Optimal Affinity construction uses the oa2x2 literal Stoichiometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L116-L119
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L116-L119

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_literalStoichiometry :
    oa2x2.xReactant = ![1, 0] ∧ oa2x2.yReactant = ![0, 2] ∧
    oa2x2.xProduct = ![0, 2] ∧ oa2x2.yProduct = ![1, 1] := by sorry
