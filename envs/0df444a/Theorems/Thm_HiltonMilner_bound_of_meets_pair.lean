-- Prove2me | Theorems.Thm_HiltonMilner_bound_of_meets_pair
-- name    : HiltonMilner.bound_of_meets_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:09:13.389103+00:00
-- url     : https://prove2.me/theorems/7029f7ba-9532-5f1c-ad3b-759b3901b5f3
-- title:
--   Hilton Milner: bound of meets pair
-- statement:
--   The case where every member meets `{y, z}`.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean#L73-L174
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean#L73-L174

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
public import Definitions.Def_HiltonMilnerLib_HMCore
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.bound_of_meets_pair {X : Finset ℕ} {n k y z : ℕ} (hX : #X = n) (hk : 2 ≤ k)
    (hn : 2 * k + 1 ≤ n) (hyX : y ∈ X) (hzX : z ∈ X) (hyz : y ≠ z) {𝒜 : Finset (Finset ℕ)}
    (h𝒜 : 𝒜 ⊆ powersetCard k X) (hc : Cross 𝒜 𝒜) (hnt : NonTriv X 𝒜)
    (hmeet : ∀ A ∈ 𝒜, y ∈ A ∨ z ∈ A) : #𝒜 ≤ hmNum n k := by sorry
