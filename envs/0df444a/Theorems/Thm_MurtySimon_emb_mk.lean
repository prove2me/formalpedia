-- Prove2me | Theorems.Thm_MurtySimon_emb_mk
-- name    : MurtySimon.emb_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:41.932403+00:00
-- url     : https://prove2.me/theorems/80e52cb6-9137-5a92-a9df-753c332b9b3d
-- title:
--   Murty Simon: emb mk
-- statement:
--   The Murty Simon construction uses the emb mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L80-L81
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L80-L81

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section

theorem MurtySimon.emb_mk (M : Finset (Sym2 V)) (v : Sym2 V) :
    emb G M ((aux G M).connectedComponentMk v) = (aux G ∅).connectedComponentMk v := by sorry
