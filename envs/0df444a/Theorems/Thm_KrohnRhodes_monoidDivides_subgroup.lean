-- Prove2me | Theorems.Thm_KrohnRhodes_monoidDivides_subgroup
-- name    : KrohnRhodes.monoidDivides_subgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:36.633982+00:00
-- url     : https://prove2.me/theorems/2ed7746a-eb9e-4dc8-896b-5e5f1ef9effb
-- title:
--   Krohn Rhodes: monoid Divides subgroup
-- statement:
--   A subgroup `N ≤ G` divides `G`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L448-L450
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L448-L450

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

theorem KrohnRhodes.monoidDivides_subgroup {G : Type u} [Group G] (N : Subgroup G) :
    KrohnRhodes.MonoidDivides (N : Type u) G := by sorry
