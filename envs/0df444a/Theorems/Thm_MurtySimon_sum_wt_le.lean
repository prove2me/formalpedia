-- Prove2me | Theorems.Thm_MurtySimon_sum_wt_le
-- name    : MurtySimon.sum_wt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:50.043662+00:00
-- url     : https://prove2.me/theorems/811b7326-e3a0-5192-983b-e77c46abf89d
-- title:
--   Murty Simon: sum wt le
-- statement:
--   **Lemma 2.7.** Each noncritical non-edge receives total weight at most `2`.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L146-L176
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L146-L176

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

theorem MurtySimon.sum_wt_le : ∑ p ∈ exits G M, wt M p ≤ 2 * #(Nc G) := by sorry
