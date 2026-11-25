-- Prove2me | Theorems.Thm_HiltonMilner_cross_bound_base
-- name    : HiltonMilner.cross_bound_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:06:06.826051+00:00
-- url     : https://prove2.me/theorems/c1df2312-933e-5157-abf0-08427a1be52b
-- title:
--   Hilton Milner: cross bound base
-- statement:
--   The base case `m = 2a`.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L111-L133
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L111-L133

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.cross_bound_base {X : Finset ℕ} {a : ℕ} (hX : #X = 2 * a) {𝒜 ℬ : Finset (Finset ℕ)}
    (h𝒜 : 𝒜 ⊆ powersetCard a X) (hℬ : ℬ ⊆ powersetCard a X) (hc : Cross 𝒜 ℬ) :
    #𝒜 + #ℬ ≤ (2 * a).choose a := by sorry
