-- Prove2me | Theorems.Thm_NashWilliams_outCut_le_card
-- name    : NashWilliams.outCut_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:19:14.385008+00:00
-- url     : https://prove2.me/theorems/a3a4bdfd-d61d-5ef9-a2cc-ed5734f07a70
-- title:
--   Nash Williams: out Cut le card
-- statement:
--   The Nash Williams construction uses the out Cut le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L195-L218
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L195-L218

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
open Classical

theorem NashWilliams.outCut_le_card [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (o : G.edgeSet → Bool)
    (S : Finset V) :
    outCut (edgeEnds G) o S ≤
      ((S ×ˢ Sᶜ).filter fun q : V × V => (toDigraph G o).Adj q.1 q.2).card := by sorry
