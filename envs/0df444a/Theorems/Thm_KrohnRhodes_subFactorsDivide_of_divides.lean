-- Prove2me | Theorems.Thm_KrohnRhodes_subFactorsDivide_of_divides
-- name    : KrohnRhodes.subFactorsDivide_of_divides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:04.053839+00:00
-- url     : https://prove2.me/theorems/64e39224-cd66-410f-b19b-c9d1759f175f
-- title:
--   Krohn Rhodes: sub Factors Divide of divides
-- statement:
--   If every factor of `factors` divides `A`, and `A` divides `M`, then every
--       factor divides `M` (transitivity of division).
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L474-L478
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L474-L478

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
open KrohnRhodes
open Green

theorem KrohnRhodes.subFactorsDivide_of_divides {A M : Type u} [Monoid A] [Monoid M]
    (hAM : KrohnRhodes.MonoidDivides A M)
    {factors : List KRFactor.{u}} (h : SubFactorsDivide A factors) :
    SubFactorsDivide M factors := by sorry
