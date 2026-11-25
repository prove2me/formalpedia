-- Prove2me | Theorems.Thm_HiltonMilner_nonempty_of_nonTriv
-- name    : HiltonMilner.nonempty_of_nonTriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:08:40.53724+00:00
-- url     : https://prove2.me/theorems/3ba8f4ab-ec14-5917-bc61-d37c3ce2d2c5
-- title:
--   Hilton Milner: nonempty of non Triv
-- statement:
--   The Hilton Milner construction uses the nonempty of non Triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean#L38-L42
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean#L38-L42

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Definitions.Def_HiltonMilnerLib_HMCore
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.nonempty_of_nonTriv {X : Finset ℕ} {𝒜 : Finset (Finset ℕ)} (hX : X.Nonempty)
    (h : NonTriv X 𝒜) : 𝒜.Nonempty := by sorry
