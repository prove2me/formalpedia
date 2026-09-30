-- Prove2me | Theorems.Thm_NumberField_artinSymbol_map_restrictNormalHom
-- name    : NumberField.artinSymbol_map_restrictNormalHom
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:47:07.431391+00:00
-- url     : https://prove2.me/theorems/40ac0f70-97ba-48c0-9546-af26e829cdd5
-- title:
--   Restriction of the Artin symbol to a normal subextension
-- statement:
--   Let $K\subseteq M\subseteq L$ be number fields with $L/K$ and $M/K$ Galois. Let $\mathfrak p$ be a nonzero prime of $K$ unramified in $L$. Under restriction of automorphisms,
--
--   $$
--   \operatorname{res}_{L,M}\bigl(\operatorname{Frob}_{\mathfrak p}(L/K)\bigr)
--   =\operatorname{Frob}_{\mathfrak p}(M/K).
--   $$
--
--   Both sides are arithmetic Frobenius conjugacy classes; $\mathfrak p$ is also unramified in $M$.
--
--   This states functoriality of Frobenius classes in a normal tower.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/ArtinSymbol.lean#L109-L140) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/ArtinSymbol.lean#L109-L140

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_RamificationInertia_Tower
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Artin symbol of an unramified prime

For a finite Galois extension of number fields, this file attaches to an unramified
prime ideal of the base the conjugacy class of its arithmetic Frobenius elements.
The definition uses Mathlib's `IsArithFrobAt` and `arithFrobAt`; no Frobenius
predicate or representative is introduced here.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9,
Exercise 2.

The same reference gives functoriality in a normal tower: restriction maps the Artin symbol of
`L/K` to the Artin symbol of `M/K`. Unramifiedness in the intermediate extension is derived from
unramifiedness in the top extension, rather than assumed separately.

Raising the base field is the companion law, and it takes a power: for `K ⊆ M ⊆ L`, the symbol
of a prime of `𝓞 M` above `𝔭`, read inside `Gal(L/K)`, is the `f(𝔓/𝔭)`-th power of the symbol of
`𝔭`. Stated on conjugacy classes it names no prime of `𝓞 L` and no Frobenius representative, both
of which the element-level form in `TauCeti.NumberTheory.NumberField.Frobenius.Tower` fixes.

Finally, the symbol detects complete splitting: it is the identity class exactly when the
residue degree is one, equivalently when `𝓞 L` has `[L : K]` primes above `𝔭`.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField _root_.Pointwise

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem NumberField.artinSymbol_map_restrictNormalHom {M L : Type*} [_root_.Field M] [_root_.NumberField M]
    [_root_.Field L] [_root_.NumberField L] [_root_.Algebra K M] [_root_.Algebra M L] [_root_.Algebra K L]
    [_root_.IsScalarTower K M L] [_root_.IsGalois K L] [_root_.IsGalois K M]
    (𝔭 : _root_.Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : _root_.Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      _root_.Algebra.IsUnramifiedAt (𝓞 K) Q) :
    _root_.ConjClasses.map (_root_.AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M)
        (_root_.NumberField.artinSymbol 𝔭 hur) =
      _root_.NumberField.artinSymbol 𝔭 (fun P _ _ ↦
        _root_.TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn (S := 𝓞 L)
          (fun Q hQ hQ' ↦ @hur Q hQ hQ') P) := by sorry
