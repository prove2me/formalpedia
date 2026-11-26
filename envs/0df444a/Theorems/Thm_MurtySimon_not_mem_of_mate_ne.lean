-- Prove2me | Theorems.Thm_MurtySimon_not_mem_of_mate_ne
-- name    : MurtySimon.not_mem_of_mate_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:33.907836+00:00
-- url     : https://prove2.me/theorems/87f526da-e193-4870-98a9-bfd65ee30e26
-- title:
--   Murty Simon: not mem of mate ne
-- statement:
--   The Murty Simon construction uses the not mem of mate ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L73-L74
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L73-L74

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}

theorem MurtySimon.not_mem_of_mate_ne {x y : V} (h : mate M x ≠ y) (hM : IsEdgeMatching G M) :
    s(x, y) ∉ M := by sorry
