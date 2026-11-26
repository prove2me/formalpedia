-- Prove2me | Theorems.Thm_KrohnRhodes_regularWreath_to_monoidWreath_injective
-- name    : KrohnRhodes.regularWreath_to_monoidWreath_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:56.610034+00:00
-- url     : https://prove2.me/theorems/52827519-e0c1-49b2-ab4d-614dd48809e5
-- title:
--   Krohn Rhodes: regular Wreath to monoid Wreath injective
-- statement:
--   The bridge is injective.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/MonoidWreathBridge.lean#L82-L105
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/MonoidWreathBridge.lean#L82-L105

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib.GroupTheory.RegularWreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
set_option autoImplicit true
@[expose] public section
public section
open KrohnRhodes
universe u
variable (D Q : Type u) [Group D] [Group Q]

theorem KrohnRhodes.regularWreath_to_monoidWreath_injective :
    Function.Injective (regularWreath_to_monoidWreath D Q) := by sorry
