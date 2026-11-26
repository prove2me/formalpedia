-- Prove2me | Theorems.Thm_MurtySimon_not_mem_Rt_of_mem_Lt
-- name    : MurtySimon.not_mem_Rt_of_mem_Lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:09.489372+00:00
-- url     : https://prove2.me/theorems/2ad28243-b82c-48e6-9054-198cba03eb5d
-- title:
--   Murty Simon: not mem Rt of mem Lt
-- statement:
--   The Murty Simon construction uses the not mem Rt of mem Lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L54-L55
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L54-L55

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

theorem MurtySimon.not_mem_Rt_of_mem_Lt {M : Finset (Sym2 V)} {e : Sym2 V} (h : e ∈ Lt G M) : e ∉ Rt G := by sorry
