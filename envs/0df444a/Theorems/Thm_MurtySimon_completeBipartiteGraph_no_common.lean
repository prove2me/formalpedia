-- Prove2me | Theorems.Thm_MurtySimon_completeBipartiteGraph_no_common
-- name    : MurtySimon.completeBipartiteGraph_no_common
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:21:32.964921+00:00
-- url     : https://prove2.me/theorems/b47f669b-432b-469b-8402-1c5db1d00a92
-- title:
--   Murty Simon: complete Bipartite Graph no common
-- statement:
--   The Murty Simon construction uses the complete Bipartite Graph no common property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L235-L238
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L235-L238

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

theorem MurtySimon.completeBipartiteGraph_no_common {A B : Type*} {p q w : A ⊕ B}
    (hpq : (completeBipartiteGraph A B).Adj p q) (hpw : (completeBipartiteGraph A B).Adj p w)
    (hwq : (completeBipartiteGraph A B).Adj w q) : False := by sorry
