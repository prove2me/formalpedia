-- Prove2me | Theorems.Thm_JinTheorem_jin_sharp
-- name    : JinTheorem.jin_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:56:45.682957+00:00
-- url     : https://prove2.me/theorems/34ef83d7-8887-5ce1-a15c-dcbc2795f521
-- title:
--   Jin Theorem: jin sharp
-- statement:
--   **Sharpness (Häggkvist 1982).** For every `m ≥ 1` there is a triangle-free `10m`-regular graph
--   on `29m` vertices that is not 3-colourable.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/Solution.lean#L37-L40
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/Solution.lean#L37-L40

module
public import Mathlib
public import Definitions.Def_JinLib_Jin
public import Definitions.Def_JinTriangleFree_Solution
public import Theorems.Thm_DenseTriangleFree_jin_sharp

set_option autoImplicit true
@[expose] public section
public section
open JinTheorem

theorem JinTheorem.jin_sharp (m : ℕ) (hm : 0 < m) :
    ∃ G : SimpleGraph (Fin (29 * m)), ∃ _ : DecidableRel G.Adj,
      G.CliqueFree 3 ∧ (∀ v, G.degree v = 10 * m) ∧ ¬ G.Colorable 3 := by sorry
