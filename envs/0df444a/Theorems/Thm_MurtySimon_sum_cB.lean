-- Prove2me | Theorems.Thm_MurtySimon_sum_cB
-- name    : MurtySimon.sum_cB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:42.876004+00:00
-- url     : https://prove2.me/theorems/daf8ea58-bf94-50ea-946f-7114fb93743b
-- title:
--   Murty Simon: sum c B
-- statement:
--   The Murty Simon construction uses the sum c B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L461-L462
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L461-L462

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

theorem MurtySimon.sum_cB (M : Finset (Sym2 V)) : ∑ C, cB G M C = #(Rt G) := by sorry
