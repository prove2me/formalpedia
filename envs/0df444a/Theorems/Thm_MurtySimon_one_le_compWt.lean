-- Prove2me | Theorems.Thm_MurtySimon_one_le_compWt
-- name    : MurtySimon.one_le_compWt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:57.531005+00:00
-- url     : https://prove2.me/theorems/fa500fb2-5d9f-4571-a69f-3dc220a80852
-- title:
--   Murty Simon: one le comp Wt
-- statement:
--   The Murty Simon construction uses the one le comp Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L200-L202
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L200-L202

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

theorem MurtySimon.one_le_compWt {C : (aux G M).ConnectedComponent} {p : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) : 1 ≤ compWt C := by sorry
