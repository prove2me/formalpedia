-- Prove2me | Theorems.Thm_MurtySimon_two_mul_card_le
-- name    : MurtySimon.two_mul_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:29.335804+00:00
-- url     : https://prove2.me/theorems/1a61a35d-db1d-42e6-a0ec-526ce769bb0a
-- title:
--   Murty Simon: two mul card le
-- statement:
--   The Murty Simon construction uses the two mul card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L34-L55
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L34-L55

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem MurtySimon.two_mul_card_le {M : Finset (Sym2 V)} (hM : IsEdgeMatching G M) :
    2 * #M ≤ Fintype.card V := by sorry
