-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_overallReaction
-- name    : OptimalAffinity.oa2x2_overallReaction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:53:48.690978+00:00
-- url     : https://prove2.me/theorems/621e0ff8-70da-4b25-8275-ae2cca395e5f
-- title:
--   Optimal Affinity: oa2x2 overall Reaction
-- statement:
--   The Optimal Affinity construction uses the oa2x2 overall Reaction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L144-L147
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L144-L147

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_overallReaction :
    alpha oa2x2 = 1 ∧ beta oa2x2 = 2 ∧
    yInput oa2x2 = 2 ∧ yOutput oa2x2 = 2 := by sorry
