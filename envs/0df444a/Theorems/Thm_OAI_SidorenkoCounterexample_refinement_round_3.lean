-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_refinement_round_3
-- name    : OAI.SidorenkoCounterexample.refinement_round_3
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-08T17:22:00.93436+00:00
-- url     : https://prove2.me/theorems/36edc310-609c-486d-8d7a-21958998b5c0
-- title:
--   Incidence color refinement, round 4
-- statement:
--   For the prescribed incidence graph, let $c_I^{(3)}$ and $c_J^{(3)}$ be the color maps specified by the refinement tables. Let $H_I^{(3)}(v,\cdot)$ and $H_J^{(3)}(v,\cdot)$ count neighboring colors using the incidence corners. The next colors satisfy
--
--   $$
--   c_I^{(4)}(v)=c_I^{(4)}(w)\iff c_I^{(3)}(v)=c_I^{(3)}(w)\ \text{and}\ H_I^{(3)}(v,\cdot)=H_I^{(3)}(w,\cdot),
--   $$
--
--   and the same equivalence holds for the face colors and their histograms. The final point and face color maps are both injective.
--
--   This certifies round 4 of the finite refinement used in the pinning theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Refinement.lean, lemmas histLeft3_correct, histRight3_correct, refineLeft3_iff and refineRight3_iff, with refineLeft_final and refineRight_final. This is their neighbor-histogram formulation as used in Pinning.lean, pinning_complex.

import Mathlib
import Definitions.Def_SidorenkoRefinementColors
open OAI.SidorenkoCounterexample

theorem OAI.SidorenkoCounterexample.refinement_round_3 :
  (∀ v w : Fin 13, refineLeft4 v = refineLeft4 w ↔
    refineLeft3 v = refineLeft3 w ∧
    neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) v =
      neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) w) ∧
  (∀ v w : Fin 22, refineRight4 v = refineRight4 w ↔
    refineRight3 v = refineRight3 w ∧
    neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft3 (cornerPoint k)) v =
      neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft3 (cornerPoint k)) w) ∧
  Function.Injective refineLeft4 ∧ Function.Injective refineRight4 := by sorry
