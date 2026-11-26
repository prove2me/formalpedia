-- Prove2me | Theorems.Thm_KrohnRhodes_monoidDivides_of_surjective
-- name    : KrohnRhodes.monoidDivides_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:10.645802+00:00
-- url     : https://prove2.me/theorems/41e9fe26-c0ab-5f12-b375-d4949bc0ac6b
-- title:
--   Krohn Rhodes: monoid Divides of surjective
-- statement:
--   A surjective monoid homomorphism `φ : M ↠ N` exhibits `N` as a quotient of
--       `M`, hence `N` divides `M`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L436-L440
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L436-L440

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

theorem KrohnRhodes.monoidDivides_of_surjective {M N : Type u} [Monoid M] [Monoid N]
    (φ : M →* N) (hφ : Function.Surjective φ) :
    KrohnRhodes.MonoidDivides N M := by sorry
