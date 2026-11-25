-- Prove2me | Theorems.Thm_HiltonMilner_mem_high
-- name    : HiltonMilner.mem_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:53:49.616564+00:00
-- url     : https://prove2.me/theorems/18d7f872-d85d-51b7-a64f-831c8d285f10
-- title:
--   Hilton Milner: mem high
-- statement:
--   The Hilton Milner construction uses the mem high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L61-L63
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L61-L63

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.mem_high {z : ℕ} {𝒜 : Finset (Finset ℕ)} {C : Finset ℕ} :
    C ∈ high z 𝒜 ↔ ∃ A ∈ 𝒜, z ∈ A ∧ A.erase z = C := by sorry
