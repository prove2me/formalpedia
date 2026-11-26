-- Prove2me | Theorems.Thm_MurtySimon_card_sdiff_eq_card_Lt
-- name    : MurtySimon.card_sdiff_eq_card_Lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:38.001677+00:00
-- url     : https://prove2.me/theorems/13fc6288-1e59-44fe-a2de-adbd778beec6
-- title:
--   Murty Simon: card sdiff eq card Lt
-- statement:
--   The Murty Simon construction uses the card sdiff eq card Lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L74-L75
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L74-L75

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

theorem MurtySimon.card_sdiff_eq_card_Lt (M : Finset (Sym2 V)) : #(G.edgeFinset \ M) = #(Lt G M) := by sorry
