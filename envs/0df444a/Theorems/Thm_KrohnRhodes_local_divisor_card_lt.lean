-- Prove2me | Theorems.Thm_KrohnRhodes_local_divisor_card_lt
-- name    : KrohnRhodes.local_divisor_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:16.323073+00:00
-- url     : https://prove2.me/theorems/fb0e314f-cab0-403b-b7cc-66f53c2f98a7
-- title:
--   Krohn Rhodes: local divisor card lt
-- statement:
--   **The local divisor at a non-unit is strictly smaller.** Let $M$ be a finite monoid and
--   $c \in M$ a non-unit. Then $|M_c| < |M|$, where $M_c$ is the local divisor
--   `LocalDivisor` $M$ $c$ (carrier $cM \cap Mc$). Cardinalities are
--   `Nat.card`; both sides are finite. (DKS §2.5: if $c$ is not a unit then $1 \notin cM \cap Mc$.)
--
--   *Proof sketch.* Pure algebra, no finiteness in the key step: if $1 = c a$ and $1 = b c$ then
--   $b = b(ca) = (bc)a = a$, so $a$ is a two-sided inverse of $c$ ($ca = 1$ and $ac = 1$) and $c$ is
--   a unit — contradiction. Hence no element of $M_c$ has value $1$: the value map
--   $M_c \hookrightarrow M$ (injective by `LocalDivisor.ext`) misses the point $1$. Transporting both
--   cardinalities through `Fintype.ofFinite` and `Nat.card_eq_fintype_card`, the
--   injection-missing-a-point counting lemma `Fintype.card_lt_of_injective_of_notMem` gives the
--   strict inequality.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L337-L358
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L337-L358

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

theorem KrohnRhodes.local_divisor_card_lt {M : Type} [Monoid M] [Finite M] {c : M} (hc : ¬ IsUnit c) :
    Nat.card (LocalDivisor M c) < Nat.card M := by sorry
