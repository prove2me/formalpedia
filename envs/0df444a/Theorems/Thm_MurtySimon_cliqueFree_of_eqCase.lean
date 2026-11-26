-- Prove2me | Theorems.Thm_MurtySimon_cliqueFree_of_eqCase
-- name    : MurtySimon.cliqueFree_of_eqCase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:13.126504+00:00
-- url     : https://prove2.me/theorems/821b7a23-6017-46ce-9f33-22ab7a1e013b
-- title:
--   Murty Simon: clique Free of eq Case
-- statement:
--   **Lemma 1.3.** An equality case is triangle-free.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L347-L364
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L347-L364

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

theorem MurtySimon.cliqueFree_of_eqCase (hG : IsCritical G) (heq : EqCase G) : G.CliqueFree 3 := by sorry
