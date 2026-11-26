-- Prove2me | Theorems.Thm_KrohnRhodes_group_sgdiv_via_normal
-- name    : KrohnRhodes.group_sgdiv_via_normal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:32.824376+00:00
-- url     : https://prove2.me/theorems/d20d5b86-1088-5e80-9fb0-34b3853e7455
-- title:
--   Krohn Rhodes: group sgdiv via normal
-- statement:
--   For a finite group `G` with a normal subgroup `N`, `G` divides
--   `WreathProduct N (G/N) (G/N)` as a semigroup.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/KrasnerKaloujnine.lean#L187-L228
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/KrasnerKaloujnine.lean#L187-L228

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Mathlib
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.RegularWreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
open KrohnRhodes
universe u
variable {G : Type u} [Group G]

theorem KrohnRhodes.group_sgdiv_via_normal {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] :
    SgDiv G (WreathProduct N (G ⧸ N) (G ⧸ N)) := by sorry
