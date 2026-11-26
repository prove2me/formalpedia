-- Prove2me | Theorems.Thm_MurtySimon_card_add_card_compl
-- name    : MurtySimon.card_add_card_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:07.535317+00:00
-- url     : https://prove2.me/theorems/6e232058-5b40-5c88-9186-4f0819f7bb6f
-- title:
--   Murty Simon: card add card compl
-- statement:
--   The Murty Simon construction uses the card add card compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L99-L121
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L99-L121

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

theorem MurtySimon.card_add_card_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset + #Gᶜ.edgeFinset = (Fintype.card V).choose 2 := by sorry
