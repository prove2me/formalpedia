-- Prove2me | Theorems.Thm_MurtySimon_two_le_compWt_single
-- name    : MurtySimon.two_le_compWt_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:06.163208+00:00
-- url     : https://prove2.me/theorems/b2d5023e-0e77-51ee-b258-45264d3e062f
-- title:
--   Murty Simon: two le comp Wt single
-- statement:
--   **Lemma 2.10.** A component consisting of a single left vertex has a safe switch exit or two
--   switch exits.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L257-L311
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L257-L311

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

theorem MurtySimon.two_le_compWt_single (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G)
    (h1 : cA G M C = 1) : 2 ≤ compWt C := by sorry
