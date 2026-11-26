-- Prove2me | Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
-- name    : MurtySimon.OnPath.mem_edgeSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:50:47.327913+00:00
-- url     : https://prove2.me/theorems/27ecbf01-722c-56e6-91c7-81d231cd4b03
-- title:
--   On Path: mem edge Set
-- statement:
--   The On Path construction uses the mem edge Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L78-L80
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L78-L80

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

theorem MurtySimon.OnPath.mem_edgeSet {e f : Sym2 V} (h : OnPath G e f) : e ∈ G.edgeSet := by sorry
