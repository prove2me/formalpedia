-- Prove2me | Theorems.Thm_HiltonMilner_sh_subset_powersetCard
-- name    : HiltonMilner.sh_subset_powersetCard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:28.402237+00:00
-- url     : https://prove2.me/theorems/3e2bc4b6-78c0-5373-bcd1-c49ffcc0aaa4
-- title:
--   Hilton Milner: sh subset powerset Card
-- statement:
--   The Hilton Milner construction uses the sh subset powerset Card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L112-L122
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L112-L122

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.sh_subset_powersetCard {y z a : ℕ} {X : Finset ℕ} {𝒜 : Finset (Finset ℕ)}
    (hy : y ∈ X) (h𝒜 : 𝒜 ⊆ powersetCard a X) : sh y z 𝒜 ⊆ powersetCard a X := by sorry
