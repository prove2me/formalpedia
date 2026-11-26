-- Prove2me | Theorems.Thm_KrohnRhodes_sgDiv_trans
-- name    : KrohnRhodes.sgDiv_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:23.004695+00:00
-- url     : https://prove2.me/theorems/195132a3-ab69-5bb6-a027-e9084b73231b
-- title:
--   Krohn Rhodes: sg Div trans
-- statement:
--   `SgDiv` is transitive.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Division.lean#L40-L78
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Division.lean#L40-L78

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

theorem KrohnRhodes.sgDiv_trans {S T U : Type u} [Mul S] [Mul T] [Mul U]
    (hST : SgDiv S T) (hTU : SgDiv T U) : SgDiv S U := by sorry
