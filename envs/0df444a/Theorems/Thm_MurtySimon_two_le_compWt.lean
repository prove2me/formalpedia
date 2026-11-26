-- Prove2me | Theorems.Thm_MurtySimon_two_le_compWt
-- name    : MurtySimon.two_le_compWt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:56.259944+00:00
-- url     : https://prove2.me/theorems/3f808e96-07c0-4736-b592-58e491bb028e
-- title:
--   Murty Simon: two le comp Wt
-- statement:
--   **Corollary 2.12** (Lemmas 2.10 and 2.11). Every left-lopsided component has weight at least
--   two.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L441-L452
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L441-L452

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
variable (hM : IsEdgeMatching G M) {C : (aux G M).ConnectedComponent}
  (hC : cA G M C = cB G M C + 1)
include hM hC

theorem MurtySimon.two_le_compWt (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) : 2 ≤ compWt C := by sorry
