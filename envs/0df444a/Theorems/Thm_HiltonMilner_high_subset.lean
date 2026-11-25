-- Prove2me | Theorems.Thm_HiltonMilner_high_subset
-- name    : HiltonMilner.high_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:20.080171+00:00
-- url     : https://prove2.me/theorems/9dd4bcea-f74b-5508-b9c0-99468941b1ca
-- title:
--   Hilton Milner: high subset
-- statement:
--   The Hilton Milner construction uses the high subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L73-L78
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L73-L78

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.high_subset {a z : ℕ} {X : Finset ℕ} {𝒜 : Finset (Finset ℕ)}
    (h𝒜 : 𝒜 ⊆ powersetCard a X) : high z 𝒜 ⊆ powersetCard (a - 1) (X.erase z) := by sorry
