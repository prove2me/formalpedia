-- Prove2me | Theorems.Thm_KrohnRhodes_MonoidDivides_trans
-- name    : KrohnRhodes.MonoidDivides.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:44.242687+00:00
-- url     : https://prove2.me/theorems/77741c87-e330-5f96-8a01-3c0b1fdd2ef8
-- title:
--   Monoid Divides: trans
-- statement:
--   **Monoid division is transitive.** If `M ≼ N` (witnessed by `S ≤ N`, `φ : S ↠ M`) and
--   `N ≼ P` (witnessed by `T ≤ P`, `ψ : T ↠ N`), then `M ≼ P`. The witnessing submonoid of `P` is
--   the image under `T ↪ P` of the pre-image `ψ⁻¹(S) ≤ T`; the surjection is `φ ∘ (ψ restricted) ∘
--   (the submonoid iso)`. This is the standard composition of "quotient of a submonoid"
--   relations.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/LocalDivisor.lean#L45-L60
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/LocalDivisor.lean#L45-L60

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
set_option autoImplicit true
@[expose] public section
public section
open FreeMonoid Computability Pointwise
universe u
variable {α : Type u}
open KrohnRhodes

theorem KrohnRhodes.MonoidDivides.trans {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (h1 : MonoidDivides M N) (h2 : MonoidDivides N P) : MonoidDivides M P := by sorry
