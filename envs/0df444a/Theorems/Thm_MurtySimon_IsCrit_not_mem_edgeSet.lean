-- Prove2me | Theorems.Thm_MurtySimon_IsCrit_not_mem_edgeSet
-- name    : MurtySimon.IsCrit.not_mem_edgeSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:50:52.648225+00:00
-- url     : https://prove2.me/theorems/f3fa8388-ab32-4721-ba12-f643be7311e0
-- title:
--   Is Crit: not mem edge Set
-- statement:
--   The Is Crit construction uses the not mem edge Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L70-L72
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L70-L72

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

theorem MurtySimon.IsCrit.not_mem_edgeSet {f : Sym2 V} (h : IsCrit G f) : f ∉ G.edgeSet := by sorry
