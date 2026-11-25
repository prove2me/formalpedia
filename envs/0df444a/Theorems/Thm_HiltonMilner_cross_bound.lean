-- Prove2me | Theorems.Thm_HiltonMilner_cross_bound
-- name    : HiltonMilner.cross_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:59:02.952012+00:00
-- url     : https://prove2.me/theorems/b2a77470-b6ca-541f-af55-3bd86cdec277
-- title:
--   Hilton Milner: cross bound
-- statement:
--   **Nonempty cross-intersecting families (Hilton–Milner).**
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L136-L262
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L136-L262

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.cross_bound (m : ℕ) : ∀ (X : Finset ℕ), #X = m → ∀ a, 1 ≤ a → 2 * a ≤ m →
    ∀ 𝒜 ℬ : Finset (Finset ℕ), 𝒜 ⊆ powersetCard a X → ℬ ⊆ powersetCard a X →
    𝒜.Nonempty → ℬ.Nonempty → Cross 𝒜 ℬ →
    #𝒜 + #ℬ ≤ m.choose a - (m - a).choose a + 1 := by sorry
