-- Prove2me | Theorems.Thm_MurtySimon_mem_Rt
-- name    : MurtySimon.mem_Rt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:50.226419+00:00
-- url     : https://prove2.me/theorems/0cc30492-3e23-5f9a-87db-b380a97e8474
-- title:
--   Murty Simon: mem Rt
-- statement:
--   The Murty Simon construction uses the mem Rt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L49-L49
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L49-L49

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

theorem MurtySimon.mem_Rt {f : Sym2 V} : f ∈ Rt G ↔ IsCrit G f := by sorry
