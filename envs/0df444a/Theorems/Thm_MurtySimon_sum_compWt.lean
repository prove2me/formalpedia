-- Prove2me | Theorems.Thm_MurtySimon_sum_compWt
-- name    : MurtySimon.sum_compWt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:02.893252+00:00
-- url     : https://prove2.me/theorems/6f09af1a-3795-5de8-b4ff-a671f280e3b2
-- title:
--   Murty Simon: sum comp Wt
-- statement:
--   The Murty Simon construction uses the sum comp Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L464-L465
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L464-L465

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

theorem MurtySimon.sum_compWt : ∑ C, compWt (G := G) (M := M) C = ∑ p ∈ exits G M, wt M p := by sorry
