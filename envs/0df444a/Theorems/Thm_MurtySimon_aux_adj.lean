-- Prove2me | Theorems.Thm_MurtySimon_aux_adj
-- name    : MurtySimon.aux_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:12.880973+00:00
-- url     : https://prove2.me/theorems/e0e984da-f8ff-4ff4-bed3-4da7fbd3af1a
-- title:
--   Murty Simon: aux adj
-- statement:
--   The Murty Simon construction uses the aux adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L104-L112
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L104-L112

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}

theorem MurtySimon.aux_adj {M : Finset (Sym2 V)} {e f : Sym2 V} :
    (aux G M).Adj e f ↔ (e ∉ M ∧ OnPath G e f) ∨ (f ∉ M ∧ OnPath G f e) := by sorry
