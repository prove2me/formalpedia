-- Prove2me | Theorems.Thm_KrohnRhodes_constEnd_mul
-- name    : KrohnRhodes.constEnd_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:56.376483+00:00
-- url     : https://prove2.me/theorems/e651cf9c-20ca-5763-abf8-8023d0779ecb
-- title:
--   Krohn Rhodes: const End mul
-- statement:
--   **A constant map absorbs on the left:** `constEnd p * t = constEnd p`
--   for every transformation `t`.  (`(constEnd p * t) x = constEnd p (t x) = p`.)
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/ConstantMaps.lean#L75-L76
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/ConstantMaps.lean#L75-L76

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.show false
open KrohnRhodes
universe u
variable {Q : Type u}

theorem KrohnRhodes.constEnd_mul (p : Q) (t : Function.End Q) :
    constEnd p * t = constEnd p := by sorry

attribute [defeq] KrohnRhodes.constEnd_mul
