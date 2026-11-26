-- Prove2me | Theorems.Thm_KrohnRhodes_exists_nonunit_generator
-- name    : KrohnRhodes.exists_nonunit_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:23.046436+00:00
-- url     : https://prove2.me/theorems/a8c219bb-884e-4be8-8e27-6a00768d2742
-- title:
--   Krohn Rhodes: exists nonunit generator
-- statement:
--   **A non-group monoid has a non-unit in every generating set.** Let $M$ be a monoid, $A$ a
--   finite generating set ($\texttt{Submonoid.closure}\,A = \top$), and suppose $M$ is not a group:
--   some $m \in M$ is not a unit. Then some $c \in A$ is not a unit. (Folklore.)
--
--   *Proof sketch.* Contrapositive: if every element of $A$ is a unit, then every element of the
--   closure is a unit, by `Submonoid.closure_induction` — $1$ is a unit and units are closed under
--   multiplication (`IsUnit.mul`); since the closure is all of $M$, this contradicts the non-unit
--   $m$.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L842-L855
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L842-L855

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

theorem KrohnRhodes.exists_nonunit_generator {M : Type} [Monoid M] {A : Finset M}
    (hA : Submonoid.closure (A : Set M) = ⊤) (hM : ∃ m : M, ¬ IsUnit m) :
    ∃ c ∈ A, ¬ IsUnit c := by sorry
