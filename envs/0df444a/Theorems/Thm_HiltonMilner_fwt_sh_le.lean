-- Prove2me | Theorems.Thm_HiltonMilner_fwt_sh_le
-- name    : HiltonMilner.fwt_sh_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:04:11.052281+00:00
-- url     : https://prove2.me/theorems/99533adb-2b97-597f-af8c-e0cd27307e57
-- title:
--   Hilton Milner: fwt sh le
-- statement:
--   The Hilton Milner construction uses the fwt sh le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L102-L105
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L102-L105

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.fwt_sh_le {y z : ℕ} (hyz : y < z) (𝒜 : Finset (Finset ℕ)) : fwt (sh y z 𝒜) ≤ fwt 𝒜 := by sorry
