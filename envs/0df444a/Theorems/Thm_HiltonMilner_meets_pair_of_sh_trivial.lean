-- Prove2me | Theorems.Thm_HiltonMilner_meets_pair_of_sh_trivial
-- name    : HiltonMilner.meets_pair_of_sh_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:09:49.460584+00:00
-- url     : https://prove2.me/theorems/f88afe92-bc3f-499e-80f8-0349dd442398
-- title:
--   Hilton Milner: meets pair of sh trivial
-- statement:
--   If a shift makes a nontrivial family trivial, every member meets the two shifted elements.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean#L45-L70
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean#L45-L70

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Definitions.Def_HiltonMilnerLib_HMCore
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.meets_pair_of_sh_trivial {X : Finset ℕ} {y z : ℕ} {𝒜 : Finset (Finset ℕ)}
    (hnt : NonTriv X 𝒜) (htr : ¬ NonTriv X (sh y z 𝒜)) :
    ∀ A ∈ 𝒜, y ∈ A ∨ z ∈ A := by sorry
