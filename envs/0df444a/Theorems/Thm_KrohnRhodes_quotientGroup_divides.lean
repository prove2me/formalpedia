-- Prove2me | Theorems.Thm_KrohnRhodes_quotientGroup_divides
-- name    : KrohnRhodes.quotientGroup_divides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:54.419958+00:00
-- url     : https://prove2.me/theorems/7a551863-d1c0-585b-811e-3e113a576ff1
-- title:
--   Krohn Rhodes: quotient Group divides
-- statement:
--   The quotient group `G/N` divides `G`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L453-L455
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L453-L455

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

theorem KrohnRhodes.quotientGroup_divides {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
    KrohnRhodes.MonoidDivides (G ⧸ N) G := by sorry
