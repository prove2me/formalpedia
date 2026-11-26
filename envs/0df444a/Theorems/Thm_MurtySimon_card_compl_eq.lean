-- Prove2me | Theorems.Thm_MurtySimon_card_compl_eq
-- name    : MurtySimon.card_compl_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:20.739832+00:00
-- url     : https://prove2.me/theorems/112bb145-6e99-4ad4-8fb1-00defb1a08aa
-- title:
--   Murty Simon: card compl eq
-- statement:
--   The Murty Simon construction uses the card compl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L77-L97
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L77-L97

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

theorem MurtySimon.card_compl_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    #Gᶜ.edgeFinset = #(Rt G) + #(Nc G) := by sorry
