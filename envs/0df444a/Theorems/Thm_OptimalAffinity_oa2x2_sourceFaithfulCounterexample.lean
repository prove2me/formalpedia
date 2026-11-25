-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_sourceFaithfulCounterexample
-- name    : OptimalAffinity.oa2x2_sourceFaithfulCounterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:26.058805+00:00
-- url     : https://prove2.me/theorems/9a51d5f2-a4ba-5834-97ae-8c93f21324e4
-- title:
--   Optimal Affinity: oa2x2 source Faithful Counterexample
-- statement:
--   The Optimal Affinity construction uses the oa2x2 source Faithful Counterexample property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Main.lean#L20-L25
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Main.lean#L20-L25

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_Main
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_sourceFaithfulCounterexample :
    ∃ (N : Network) (x y : ℝ),
      SourceValid N ∧ IsUniqueGlobalMaximum N x y ∧
      affinityExp N x y < seedRatio N := by sorry
