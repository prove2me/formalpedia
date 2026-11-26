-- Prove2me | Theorems.Thm_MurtySimon_card_edgeSet_completeBipartiteGraph
-- name    : MurtySimon.card_edgeSet_completeBipartiteGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:21:30.131115+00:00
-- url     : https://prove2.me/theorems/a28dc531-23b4-551b-9da9-0a4ea1707548
-- title:
--   Murty Simon: card edge Set complete Bipartite Graph
-- statement:
--   For every `n`, `K_{⌈n/2⌉,⌊n/2⌋}` has `⌊n²/4⌋` edges.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L266-L292
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L266-L292

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

theorem MurtySimon.card_edgeSet_completeBipartiteGraph (n : ℕ) :
    Nat.card (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))).edgeSet = n ^ 2 / 4 := by sorry
