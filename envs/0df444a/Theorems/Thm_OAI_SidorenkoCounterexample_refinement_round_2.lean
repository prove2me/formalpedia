-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_refinement_round_2
-- name    : OAI.SidorenkoCounterexample.refinement_round_2
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-08T17:21:49.791028+00:00
-- url     : https://prove2.me/theorems/6e0e2d21-7dc9-448c-98e8-802df5d83565
-- title:
--   Incidence color refinement, round 3
-- statement:
--   For the prescribed incidence graph, let $c_I^{(2)}$ and $c_J^{(2)}$ be the color maps specified by the refinement tables. Let $H_I^{(2)}(v,\cdot)$ and $H_J^{(2)}(v,\cdot)$ count neighboring colors using the incidence corners. The next colors satisfy
--
--   $$
--   c_I^{(3)}(v)=c_I^{(3)}(w)\iff c_I^{(2)}(v)=c_I^{(2)}(w)\ \text{and}\ H_I^{(2)}(v,\cdot)=H_I^{(2)}(w,\cdot),
--   $$
--
--   and the same equivalence holds for the face colors and their histograms.
--
--   This certifies round 3 of the finite refinement used in the pinning theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Refinement.lean, lemmas histLeft2_correct, histRight2_correct, refineLeft2_iff and refineRight2_iff. This is their neighbor-histogram formulation as used in Pinning.lean, pinning_complex.

import Mathlib
import Definitions.Def_SidorenkoRefinementColors
open OAI.SidorenkoCounterexample

theorem OAI.SidorenkoCounterexample.refinement_round_2 :
  (∀ v w : Fin 13, refineLeft3 v = refineLeft3 w ↔
    refineLeft2 v = refineLeft2 w ∧
    neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) v =
      neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) w) ∧
  (∀ v w : Fin 22, refineRight3 v = refineRight3 w ↔
    refineRight2 v = refineRight2 w ∧
    neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft2 (cornerPoint k)) v =
      neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft2 (cornerPoint k)) w) := by sorry
