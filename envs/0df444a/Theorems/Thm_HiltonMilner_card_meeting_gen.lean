-- Prove2me | Theorems.Thm_HiltonMilner_card_meeting_gen
-- name    : HiltonMilner.card_meeting_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:10:48.519381+00:00
-- url     : https://prove2.me/theorems/5e9b281e-5c86-45a5-8528-e55a02deb704
-- title:
--   Hilton Milner: card meeting gen
-- statement:
--   The number of `r`-subsets of `Y` meeting `B ⊆ Y`, over any type.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HiltonMilner.lean#L36-L50
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HiltonMilner.lean#L36-L50

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.card_meeting_gen {α : Type*} [DecidableEq α] {Y B : Finset α} (hBY : B ⊆ Y) (r : ℕ) :
    #((powersetCard r Y).filter (fun D => (D ∩ B).Nonempty)) =
      (#Y).choose r - (#Y - #B).choose r := by sorry
