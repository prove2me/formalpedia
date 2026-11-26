-- Prove2me | Theorems.Thm_KrohnRhodes_LocalDivisor_localDivides
-- name    : KrohnRhodes.LocalDivisor.localDivides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:02.374238+00:00
-- url     : https://prove2.me/theorems/7adec104-753e-43f3-b40c-4cc8c43fc85d
-- title:
--   Local Divisor: local Divides
-- statement:
--   **The local divisor `M_c` divides `M`.** The witnessing submonoid is
--   `S = {t : M | c·t ∈ Mc}` (so that `c·t ∈ cM ∩ Mc`), and the surjection is `γ(t) = c·t`.
--   This is a monoid homomorphism for the twisted product, and every `x ∈ cM ∩ Mc` is `γ(a)` for the
--   witness `a` of `x ∈ cM`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/LocalDivisor.lean#L160-L193
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/LocalDivisor.lean#L160-L193

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
open KrohnRhodes.LocalDivisor
variable {M : Type*} [Monoid M] {c : M}

theorem KrohnRhodes.LocalDivisor.localDivides : MonoidDivides (LocalDivisor M c) M := by sorry
