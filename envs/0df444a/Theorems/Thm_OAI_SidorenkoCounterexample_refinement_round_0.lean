-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_refinement_round_0
-- name    : OAI.SidorenkoCounterexample.refinement_round_0
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-08T17:22:46.430875+00:00
-- url     : https://prove2.me/theorems/8a316b83-fcfe-4c7d-b7b9-a05b320bea76
-- title:
--   Incidence color refinement, round 1
-- statement:
--   For the prescribed incidence graph, let $c_I^{(0)}$ and $c_J^{(0)}$ be the color maps specified by the refinement tables. Let $H_I^{(0)}(v,\cdot)$ and $H_J^{(0)}(v,\cdot)$ count neighboring colors using the incidence corners. The next colors satisfy
--
--   $$
--   c_I^{(1)}(v)=c_I^{(1)}(w)\iff c_I^{(0)}(v)=c_I^{(0)}(w)\ \text{and}\ H_I^{(0)}(v,\cdot)=H_I^{(0)}(w,\cdot),
--   $$
--
--   and the same equivalence holds for the face colors and their histograms.
--
--   This certifies round 1 of the finite refinement used in the pinning theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Refinement.lean, lemmas histLeft0_correct, histRight0_correct, refineLeft0_iff and refineRight0_iff. This is their neighbor-histogram formulation as used in Pinning.lean, pinning_complex.

import Mathlib
import Definitions.Def_SidorenkoRefinementColors
open OAI.SidorenkoCounterexample

theorem OAI.SidorenkoCounterexample.refinement_round_0 :
  (∀ v w : Fin 13, refineLeft1 v = refineLeft1 w ↔
    refineLeft0 v = refineLeft0 w ∧
    neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) v =
      neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) w) ∧
  (∀ v w : Fin 22, refineRight1 v = refineRight1 w ↔
    refineRight0 v = refineRight0 w ∧
    neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft0 (cornerPoint k)) v =
      neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft0 (cornerPoint k)) w) := by sorry
