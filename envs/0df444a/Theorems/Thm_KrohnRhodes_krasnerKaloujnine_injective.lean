-- Prove2me | Theorems.Thm_KrohnRhodes_krasnerKaloujnine_injective
-- name    : KrohnRhodes.krasnerKaloujnine_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:55.031578+00:00
-- url     : https://prove2.me/theorems/1ac0cbad-e3e2-4b1b-a01c-775409445df1
-- title:
--   Krohn Rhodes: krasner Kaloujnine injective
-- statement:
--   Injectivity of the Krasner-Kaloujnine embedding.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/KrasnerKaloujnine.lean#L144-L179
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/KrasnerKaloujnine.lean#L144-L179

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
variable (N : Subgroup G) [N.Normal]

theorem KrohnRhodes.krasnerKaloujnine_injective :
    Function.Injective (krasnerKaloujnine_hom N) := by sorry
