-- Prove2me | Theorems.Thm_HiltonMilner_hm_bound
-- name    : HiltonMilner.hm_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:10:01.148617+00:00
-- url     : https://prove2.me/theorems/6dd1e5e0-6fe5-5301-b937-5453fbab3b90
-- title:
--   Hilton Milner: hm bound
-- statement:
--   **The Hilton–Milner bound.**
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean#L177-L334
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean#L177-L334

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Definitions.Def_HiltonMilnerLib_HMCore
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.hm_bound (n : ℕ) : ∀ (k : ℕ), 2 ≤ k → 2 * k ≤ n → ∀ (X : Finset ℕ), #X = n →
    ∀ 𝒜 : Finset (Finset ℕ), 𝒜 ⊆ powersetCard k X → Cross 𝒜 𝒜 → NonTriv X 𝒜 →
    #𝒜 ≤ hmNum n k := by sorry
