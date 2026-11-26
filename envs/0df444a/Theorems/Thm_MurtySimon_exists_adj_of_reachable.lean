-- Prove2me | Theorems.Thm_MurtySimon_exists_adj_of_reachable
-- name    : MurtySimon.exists_adj_of_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:23.262851+00:00
-- url     : https://prove2.me/theorems/64e38f83-596d-40cf-ae8c-f1d986495562
-- title:
--   Murty Simon: exists adj of reachable
-- statement:
--   The Murty Simon construction uses the exists adj of reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L84-L89
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L84-L89

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

theorem MurtySimon.exists_adj_of_reachable {W : Type*} {H : SimpleGraph W} {v w : W} (h : H.Reachable v w)
    (hne : v ≠ w) : ∃ z, H.Adj v z := by sorry
