-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_uniqueGlobalMaximum
-- name    : OptimalAffinity.oa2x2_uniqueGlobalMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:56:49.003157+00:00
-- url     : https://prove2.me/theorems/8f2c5060-746f-5728-ad93-6bd30986ec82
-- title:
--   Optimal Affinity: oa2x2 unique Global Maximum
-- statement:
--   The Optimal Affinity construction uses the oa2x2 unique Global Maximum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/GlobalMaximum.lean#L72-L79
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/GlobalMaximum.lean#L72-L79

module
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_uniqueGlobalMaximum : IsUniqueGlobalMaximum oa2x2 1 1 := by sorry
