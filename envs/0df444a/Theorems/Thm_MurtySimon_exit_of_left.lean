-- Prove2me | Theorems.Thm_MurtySimon_exit_of_left
-- name    : MurtySimon.exit_of_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:17.892942+00:00
-- url     : https://prove2.me/theorems/67347a74-0f3f-5dab-84d7-6ba418340c0f
-- title:
--   Murty Simon: exit of left
-- statement:
--   **Lemma 2.9.** Switching a left vertex of a left-lopsided component gives a noncritical
--   non-edge, hence a switch exit.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L233-L253
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L233-L253

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

theorem MurtySimon.exit_of_left {a b : V} (ha : Covered M a) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hL : s(mate M a, b) ∈ Lt G M) (hLC : (aux G M).connectedComponentMk s(mate M a, b) = C) :
    (a, b) ∈ exits G M ∧ compOf G M (a, b) = C := by sorry
