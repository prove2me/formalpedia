-- Prove2me | Theorems.Thm_KrohnRhodes_mem_reset_submonoid
-- name    : KrohnRhodes.mem_reset_submonoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:34.778866+00:00
-- url     : https://prove2.me/theorems/055a8e0d-7259-4c66-bc25-e6f29e0dd4e9
-- title:
--   Krohn Rhodes: mem reset submonoid
-- statement:
--   **Membership in the reset submonoid: identity or constant.** For every transformation
--   $t \in \mathrm{End}(Q)$ of a type $Q$: $t$ lies in the reset submonoid `resetSubmonoid` if and
--   only if $t = 1$ or $t$ is a constant map (the predicate `IsConstEnd`:
--   $\exists q,\ t = \overline{q}$).
--
--   *Proof sketch.* Right-to-left: $1$ belongs to every submonoid, and every constant map is a
--   generator (`Submonoid.subset_closure`). Left-to-right: induction over the submonoid closure
--   (`Submonoid.closure_induction`): a generator is a constant (`isConstEnd_constEnd`); $1$ is the
--   left disjunct; and for a product $x \cdot y$ with both factors identity-or-constant, either
--   $x = 1$ — then the product is $y$ and the inductive hypothesis for $y$ applies — or
--   $x = \overline{p}$ is constant and absorbs $y$ on the left by the left-zero law
--   (`constEnd_mul`: $\overline{p} \cdot y = \overline{p}$), so the product
--   is again a constant. This is the closure computation of DKS §2.4.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L86-L101
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L86-L101

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

theorem KrohnRhodes.mem_reset_submonoid (Q : Type) (t : Function.End Q) :
    t ∈ resetSubmonoid Q ↔ t = 1 ∨ IsConstEnd t := by sorry
