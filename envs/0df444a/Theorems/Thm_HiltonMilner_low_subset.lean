-- Prove2me | Theorems.Thm_HiltonMilner_low_subset
-- name    : HiltonMilner.low_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:35.558548+00:00
-- url     : https://prove2.me/theorems/ddc5a4b0-e83f-4c70-a9f7-2ac2562f0c4d
-- title:
--   Hilton Milner: low subset
-- statement:
--   The Hilton Milner construction uses the low subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L65-L71
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L65-L71

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.low_subset {a z : ℕ} {X : Finset ℕ} {𝒜 : Finset (Finset ℕ)} (h𝒜 : 𝒜 ⊆ powersetCard a X) :
    low z 𝒜 ⊆ powersetCard a (X.erase z) := by sorry
