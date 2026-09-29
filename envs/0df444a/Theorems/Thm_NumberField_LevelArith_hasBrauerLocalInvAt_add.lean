-- Prove2me | Theorems.Thm_NumberField_LevelArith_hasBrauerLocalInvAt_add
-- name    : NumberField.LevelArith.hasBrauerLocalInvAt_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/40d53627-bc2f-5a8f-ad0b-a405165f9cb6
-- title:
--   Additivity of Brauer local invariants at a place
-- statement:
--   Let $p$ be a prime and $S$ a finite set of rational primes with $p \in S$ (via `pPrime p`). Let $L$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, finite over $\mathbb{Q}$, satisfying `L.IsUnramifiedOutside S`, i.e. $L$ is finite over $\mathbb{Q}$ and for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$; assume moreover that if $p = 2$ then $L$ contains an element $i$ with $i^2 = -1$. Let $a$ and $b$ be elements of the $p$-power torsion submodule (`Submodule.torsion'` for the powers of $p$ in $\mathbb{Z}$) of `continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)`, the quotient of the $S$-level $2$-cocycles by the $S$-level $2$-coboundaries of the $\mathbb{Z}$-representation of $L.fixingSubgroup$ on the $S$-units inside $\overline{\mathbb{Q}}^{\times}$. Let $v$ be a height-one prime of $\mathcal{O}_L$ lying over some prime of $S$, i.e. an element of `placesOverPrimes`, and let $t, t'$ lie in $\mathbb{Q}/\mathbb{Z} =$ `AddCircle (1 : ℚ)`. If `HasBrauerLocalInvAt p S L a v t` and `HasBrauerLocalInvAt p S L b v t'` hold, then `HasBrauerLocalInvAt p S L (a + b) v (t + t')` holds. Here `HasBrauerLocalInvAt p S L a v t` asserts the existence of a package (all data and compatibilities summarised here): a finite normal extension $F/\mathbb{Q}$ with $L \le F$, unramified outside $S$, such that the level field of $F$ over $L$ is Galois over $L$; an identification $\iota$ of its Galois group with the quotient of the fixing subgroup of $L$ by that of $F$, compatible with `levelGal`; a bijective morphism $\varphi$ from the restriction along $\iota$ of the $F$-invariants quotient representation to the $S$-units representation of the level field, compatible with the underlying values; a Galois descent datum $D$ on the adèles of the level field together with a compatible action on its unit group; the map $j$ induced by principal idèles; and a $2$-cocycle $f$ whose inflation (`continuousH2SrInflation`) represents $a$, such that the image of the class of $f$ under the map induced by $\iota$ and $\varphi$ followed by $j$ has local invariant $t$ at $v$ in the sense of [`NumberField.IdeleLocalInv.HasLocalInv`](def/NumberField_IdeleLocalInvariant.html#L14), i.e. its local component at a place $w$ above $v$ equals $n$ times a local fundamental class and $t$ is the class of $n$ divided by the order of the decomposition group. The parameter $p$ enters only through the module in which $a$ and $b$ live.
--
--   This is the additivity of the local invariant map at a place above $S$ on the $p$-primary part of the Brauer group of $\mathcal{O}_{L,S}$, formulated for the relational predicate `HasBrauerLocalInvAt` rather than for a function. It is used by [`NumberField.LevelArith.exists_isBrauerLocalInv`](thm.html#NumberField.LevelArith.exists_isBrauerLocalInv), where the local invariants of such classes are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_hasBrauerLocalInvAt_add.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation
open NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.hasBrauerLocalInvAt_add
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (a b : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) (v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) (t t' : AddCircle (1 : ℚ))
    (ha : HasBrauerLocalInvAt p S L a v t) (hb : HasBrauerLocalInvAt p S L b v t') :
    HasBrauerLocalInvAt p S L (a + b) v (t + t') := by sorry
