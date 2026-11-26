-- Prove2me | Theorems.Thm_KrohnRhodes_monoid_faithful_self
-- name    : KrohnRhodes.monoid_faithful_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:39.909493+00:00
-- url     : https://prove2.me/theorems/21f3abf1-4169-4370-9dc9-5ee3bd35fc35
-- title:
--   Krohn Rhodes: monoid faithful self
-- statement:
--   **Every monoid acts faithfully on itself.**  The left-regular
--   representation `MulAction.toEndHom : N →* Function.End N` (sending `n` to
--   left-multiplication by `n`) is injective: `n` is recovered as the image of
--   `1` under left-multiplication by `n`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Cayley.lean#L41-L53
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Cayley.lean#L41-L53

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
set_option autoImplicit true
@[expose] public section
public section
set_option linter.style.show false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
open KrohnRhodes
universe u
variable {M : Type u} [Monoid M] [Finite M]

theorem KrohnRhodes.monoid_faithful_self (N : Type u) [Monoid N] :
    Function.Injective (MulAction.toEndHom (M := N) (α := N)) := by sorry
