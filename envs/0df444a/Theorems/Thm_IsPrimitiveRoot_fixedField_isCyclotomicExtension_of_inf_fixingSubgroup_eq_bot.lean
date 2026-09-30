-- Prove2me | Theorems.Thm_IsPrimitiveRoot_fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot
-- name    : IsPrimitiveRoot.fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:45:32.601304+00:00
-- url     : https://prove2.me/theorems/142dc2bc-5906-4707-a491-2180e5a4a265
-- title:
--   A fixed-field criterion for a cyclotomic extension
-- statement:
--   Let $M/K$ be a finite Galois extension of fields containing a primitive $m$-th root of unity, where $m\ge1$. Put $F=K(\mu_m)\subseteq M$. For a subgroup $H\le\operatorname{Gal}(M/K)$ satisfying
--
--   $$
--   H\cap\operatorname{Gal}(M/F)=\{1\},
--   $$
--
--   the fixed field $E=M^H$ satisfies
--
--   $$
--   M=E(\mu_m).
--   $$
--
--   This criterion recognizes cyclotomic extensions over intermediate fixed fields using the intersection of two Galois subgroups.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Cyclotomic/FixedField.lean#L42-L65) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Cyclotomic/FixedField.lean#L42-L65

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The fixed field of a subgroup meeting the cyclotomic fixers trivially

If `M` contains a primitive `m`-th root of unity and a subgroup `H ≤ Gal(M/K)` meets
`Gal(M/K(μ_m))` trivially, then `M` is an `m`-th cyclotomic extension of the fixed field `M ^ H`.

Only `M / K` is assumed finite and Galois. The root of unity enters as a hypothesis rather than
through an ambient cyclotomic tower, so no separately quantified intermediate field or cyclotomic
tower appears among the arguments — the fixed field itself is of course an `IntermediateField K M`,
being the base of the conclusion.

Nothing here needs `H` to be cyclic. The Chebotarev application takes `H = Subgroup.zpowers (σ, τ)`,
but the argument is the Galois correspondence and uses neither a generator nor cyclicity.

## Main results

* `IsPrimitiveRoot.fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot`

## Provenance

The proof is adapted from the private `compositum_isCyclotomic_over_fixedField` in
`CebotarevDensity/Abelian.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. That version is stated for
a cyclic subgroup over a tower `K ⊆ L ⊆ M` of number fields; the hypotheses here are weaker.
-/

 section

open IntermediateField

theorem IsPrimitiveRoot.fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot
    {K M : Type*} [_root_.Field K] [_root_.Field M] [_root_.Algebra K M] [_root_.FiniteDimensional K M] [_root_.IsGalois K M]
    {m : ℕ} [_root_.NeZero m] {ζ : M} (hζ : _root_.IsPrimitiveRoot ζ m) (H : _root_.Subgroup (M ≃ₐ[K] M))
    (hmeet : H ⊓ (_root_.IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    _root_.IsCyclotomicExtension {m} (_root_.IntermediateField.fixedField H) M := by sorry
