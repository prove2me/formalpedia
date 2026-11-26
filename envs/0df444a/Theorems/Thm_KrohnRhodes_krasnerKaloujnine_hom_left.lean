-- Prove2me | Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
-- name    : KrohnRhodes.krasnerKaloujnine_hom_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:47.436253+00:00
-- url     : https://prove2.me/theorems/cdcfd7b1-6650-475e-9bd0-8d992a5578f9
-- title:
--   Krohn Rhodes: krasner Kaloujnine hom left
-- statement:
--   The Krohn Rhodes construction uses the krasner Kaloujnine hom left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/KrasnerKaloujnine.lean#L139-L141
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/KrasnerKaloujnine.lean#L139-L141

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

theorem KrohnRhodes.krasnerKaloujnine_hom_left (g : G) (q : G ⧸ N) :
    ((krasnerKaloujnine_hom N g).left q : G) =
      (section_ N q)⁻¹ * g * section_ N ((QuotientGroup.mk' N g)⁻¹ * q) := by sorry

attribute [defeq] KrohnRhodes.krasnerKaloujnine_hom_left
