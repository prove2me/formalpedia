-- Prove2me | Theorems.Thm_KrohnRhodes_submonoid_divides
-- name    : KrohnRhodes.submonoid_divides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:32.39632+00:00
-- url     : https://prove2.me/theorems/d0a6eee6-37ad-421d-88e4-7c7421a7e7f3
-- title:
--   Krohn Rhodes: submonoid divides
-- statement:
--   **A submonoid divides its ambient monoid.** For every submonoid $N$ of a monoid $M$, the
--   subtype monoid $N$ divides $M$ in the sense of `MonoidDivides` (a
--   surjective monoid homomorphism from a submonoid of $M$ onto $N$). Used by `dks_aux` to transport
--   the simple-group divisibility guarantee from the recursive base factor $(Q \sqcup N, N)$ up to
--   $M$.
--
--   *Proof sketch.* Witness: the submonoid $N$ itself with the identity homomorphism, which is
--   surjective onto the subtype.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L806-L808
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L806-L808

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green

theorem KrohnRhodes.submonoid_divides {M : Type} [Monoid M] (N : Submonoid M) :
    KrohnRhodes.MonoidDivides ↥N M := by sorry
