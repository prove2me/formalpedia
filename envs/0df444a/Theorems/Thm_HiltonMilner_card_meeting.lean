-- Prove2me | Theorems.Thm_HiltonMilner_card_meeting
-- name    : HiltonMilner.card_meeting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:16.651672+00:00
-- url     : https://prove2.me/theorems/4c763c62-edc4-4ce9-9cd1-714bd4ed1437
-- title:
--   Hilton Milner: card meeting
-- statement:
--   The number of `r`-subsets of `Y` meeting `B ⊆ Y`.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L27-L41
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L27-L41

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.card_meeting {Y B : Finset ℕ} (hBY : B ⊆ Y) (r : ℕ) :
    #((powersetCard r Y).filter (fun D => (D ∩ B).Nonempty)) =
      (#Y).choose r - (#Y - #B).choose r := by sorry
