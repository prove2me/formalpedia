-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_refinement_round_1
-- name    : OAI.SidorenkoCounterexample.refinement_round_1
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-08T17:22:12.201521+00:00
-- url     : https://prove2.me/theorems/822ecf54-1ef8-4dee-875e-2fab37e77460
-- title:
--   Incidence color refinement, round 2
-- statement:
--   For the prescribed incidence graph, let $c_I^{(1)}$ and $c_J^{(1)}$ be the color maps specified by the refinement tables. Let $H_I^{(1)}(v,\cdot)$ and $H_J^{(1)}(v,\cdot)$ count neighboring colors using the incidence corners. The next colors satisfy
--
--   $$
--   c_I^{(2)}(v)=c_I^{(2)}(w)\iff c_I^{(1)}(v)=c_I^{(1)}(w)\ \text{and}\ H_I^{(1)}(v,\cdot)=H_I^{(1)}(w,\cdot),
--   $$
--
--   and the same equivalence holds for the face colors and their histograms.
--
--   This certifies round 2 of the finite refinement used in the pinning theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Refinement.lean, lemmas histLeft1_correct, histRight1_correct, refineLeft1_iff and refineRight1_iff. This is their neighbor-histogram formulation as used in Pinning.lean, pinning_complex.

import Mathlib
import Definitions.Def_SidorenkoRefinementColors
open OAI.SidorenkoCounterexample

theorem OAI.SidorenkoCounterexample.refinement_round_1 :
  (∀ v w : Fin 13, refineLeft2 v = refineLeft2 w ↔
    refineLeft1 v = refineLeft1 w ∧
    neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) v =
      neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) w) ∧
  (∀ v w : Fin 22, refineRight2 v = refineRight2 w ↔
    refineRight1 v = refineRight1 w ∧
    neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft1 (cornerPoint k)) v =
      neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft1 (cornerPoint k)) w) := by sorry
