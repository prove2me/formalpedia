-- Prove2me | Theorems.Thm_KrohnRhodes_sgDiv_of_injective_monoidHom
-- name    : KrohnRhodes.sgDiv_of_injective_monoidHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:44.541678+00:00
-- url     : https://prove2.me/theorems/27eedce7-689c-473d-8905-1ed3554aaecb
-- title:
--   Krohn Rhodes: sg Div of injective monoid Hom
-- statement:
--   An *injective* monoid homomorphism `f : A →* T` exhibits `A` as a
--   divisor of `T`: the subsemigroup `MonoidHom.mrange f` together with the
--   inverse (via `Function.invFun`) is a surjective `→ₙ*` onto `A`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Division.lean#L83-L101
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Division.lean#L83-L101

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
variable {M : Type u} [Monoid M] [Finite M] [DecidableEq M]

theorem KrohnRhodes.sgDiv_of_injective_monoidHom {A T : Type u} [Monoid A] [Monoid T]
    (f : A →* T) (hf : Function.Injective f) : SgDiv A T := by sorry
