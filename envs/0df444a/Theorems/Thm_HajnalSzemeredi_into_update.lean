-- Prove2me | Theorems.Thm_HajnalSzemeredi_into_update
-- name    : HajnalSzemeredi.into_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:38.397705+00:00
-- url     : https://prove2.me/theorems/89cbb30c-4674-499a-be3a-ca5a4c952183
-- title:
--   Hajnal Szemeredi: into update
-- statement:
--   The Hajnal Szemeredi construction uses the into update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L153-L158
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L153-L158

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

theorem HajnalSzemeredi.into_update {P : Finset ℕ} (h : Into S c P) (hj : j ∈ P) :
    Into S (Function.update c v j) P := by sorry
