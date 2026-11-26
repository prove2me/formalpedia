-- Prove2me | Theorems.Thm_MurtySimon_two_le_edist
-- name    : MurtySimon.two_le_edist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:21:47.602421+00:00
-- url     : https://prove2.me/theorems/4432fb2f-aa16-42dc-9a8b-d354971017e4
-- title:
--   Murty Simon: two le edist
-- statement:
--   The Murty Simon construction uses the two le edist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L223-L233
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L223-L233

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

theorem MurtySimon.two_le_edist {W : Type*} {H : SimpleGraph W} {u v : W} (hne : u ≠ v) (hn : ¬ H.Adj u v) :
    2 ≤ H.edist u v := by sorry
