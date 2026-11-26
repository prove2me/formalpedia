-- Prove2me | Theorems.Thm_KrohnRhodes_subFactorsDivide_append
-- name    : KrohnRhodes.subFactorsDivide_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:41.944897+00:00
-- url     : https://prove2.me/theorems/cd24c4cd-d81b-4dd8-8fc1-26b7ba802346
-- title:
--   Krohn Rhodes: sub Factors Divide append
-- statement:
--   The append of two divides-witnessed factor lists.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L481-L488
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L481-L488

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

theorem KrohnRhodes.subFactorsDivide_append {M : Type u} [Monoid M]
    {towA towB : List KRFactor.{u}}
    (hA : SubFactorsDivide M towA) (hB : SubFactorsDivide M towB) :
    SubFactorsDivide M (towA ++ towB) := by sorry
