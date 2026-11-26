-- Prove2me | Theorems.Thm_HajnalSzemeredi_proper_update
-- name    : HajnalSzemeredi.proper_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:32.580165+00:00
-- url     : https://prove2.me/theorems/e0f15d07-f591-4b7a-b530-ec11d46683e6
-- title:
--   Hajnal Szemeredi: proper update
-- statement:
--   Mover un vértice movible preserva la propiedad.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L161-L175
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L161-L175

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} (G : SimpleGraph V)
variable {G}
variable {S : Finset V} {c : V → ℕ} {v : V} {j : ℕ}

theorem HajnalSzemeredi.proper_update (h : Proper G S c) (hmov : Movable G S c v j) :
    Proper G S (Function.update c v j) := by sorry
