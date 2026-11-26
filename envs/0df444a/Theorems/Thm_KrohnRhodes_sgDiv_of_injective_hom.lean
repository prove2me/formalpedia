-- Prove2me | Theorems.Thm_KrohnRhodes_sgDiv_of_injective_hom
-- name    : KrohnRhodes.sgDiv_of_injective_hom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:05.695418+00:00
-- url     : https://prove2.me/theorems/69db3821-3ee0-4165-8a42-6fa07a40b89f
-- title:
--   Krohn Rhodes: sg Div of injective hom
-- statement:
--   If `S` divides `T` and there is an injective semigroup homomorphism
--   `ι : T →ₙ* W`, then `S` divides `W`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Division.lean#L117-L136
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Division.lean#L117-L136

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
open KrohnRhodes
universe u

theorem KrohnRhodes.sgDiv_of_injective_hom {S T W : Type u} [Mul S] [Mul T] [Mul W]
    (h : SgDiv S T) (ι : T →ₙ* W) (hι : Function.Injective ι) :
    SgDiv S W := by sorry
