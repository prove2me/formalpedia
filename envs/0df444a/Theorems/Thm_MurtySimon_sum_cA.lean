-- Prove2me | Theorems.Thm_MurtySimon_sum_cA
-- name    : MurtySimon.sum_cA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:33.130924+00:00
-- url     : https://prove2.me/theorems/3b2f6aed-d19f-5d38-a35e-927d55073593
-- title:
--   Murty Simon: sum c A
-- statement:
--   The Murty Simon construction uses the sum c A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L458-L459
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L458-L459

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

theorem MurtySimon.sum_cA (M : Finset (Sym2 V)) : ∑ C, cA G M C = #(Lt G M) := by sorry
