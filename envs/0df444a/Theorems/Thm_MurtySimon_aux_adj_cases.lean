-- Prove2me | Theorems.Thm_MurtySimon_aux_adj_cases
-- name    : MurtySimon.aux_adj_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:55.106062+00:00
-- url     : https://prove2.me/theorems/ae119cf2-3ebe-59e8-af42-41ed7e7f1d1e
-- title:
--   Murty Simon: aux adj cases
-- statement:
--   The Murty Simon construction uses the aux adj cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L57-L61
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L57-L61

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

theorem MurtySimon.aux_adj_cases {M : Finset (Sym2 V)} {e f : Sym2 V} (h : (aux G M).Adj e f) :
    (e ∈ Lt G M ∧ f ∈ Rt G ∧ OnPath G e f) ∨ (f ∈ Lt G M ∧ e ∈ Rt G ∧ OnPath G f e) := by sorry
