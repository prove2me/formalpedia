-- Prove2me | Theorems.Thm_MurtySimon_card_neighborFinset_right_le
-- name    : MurtySimon.card_neighborFinset_right_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:11.59886+00:00
-- url     : https://prove2.me/theorems/3064e52d-26ac-4c5d-bede-b37052ce963e
-- title:
--   Murty Simon: card neighbor Finset right le
-- statement:
--   The Murty Simon construction uses the card neighbor Finset right le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L75-L82
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L75-L82

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section

theorem MurtySimon.card_neighborFinset_right_le {M : Finset (Sym2 V)} {f : Sym2 V} (hf : f ∈ Rt G) :
    #((aux G M).neighborFinset f) ≤ 2 := by sorry
