-- Prove2me | Theorems.Thm_MurtySimon_card_edgeFinset_le
-- name    : MurtySimon.card_edgeFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:15.95239+00:00
-- url     : https://prove2.me/theorems/4cea9aed-62a0-59bb-a6c8-d24b50a14382
-- title:
--   Murty Simon: card edge Finset le
-- statement:
--   **Theorem 1.1**, the bound: an `n`-vertex diameter-2-critical graph has at most `⌊n²/4⌋`
--   edges.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L155-L161
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L155-L161

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

theorem MurtySimon.card_edgeFinset_le (hG : IsDiameterTwoCritical G) :
    #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by sorry
