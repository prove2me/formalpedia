-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_hasBrauerLocalInvAt
-- name    : NumberField.LevelArith.exists_hasBrauerLocalInvAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/dceae81b-770a-5440-bd9f-4f6cbb5d1c1d
-- title:
--   Existence of a local Brauer invariant at a place above S
-- statement:
--   Let $p$ be a prime, let $S$ be a finite set of rational primes containing $p$ (as the element `pPrime p` of `Nat.Primes`), and let $L$ be a finite-dimensional intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is unramified outside $S$, in the sense that $L/\mathbb{Q}$ is finite and, for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$; assume moreover that if $p = 2$ then $L$ contains an element $i$ with $i^2 = -1$. Let $a$ be an element of the $p$-power torsion submodule, `Submodule.torsion' ℤ _ (Submonoid.powers (p : ℤ))`, of the $\mathbb{Z}$-module `continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)`, the quotient of the $S$-level $2$-cocycles `levelCocyclesSr₂` by the level coboundaries `levelCoboundariesSr₂`, for the representation of the fixing subgroup of $L$ on the maximal $S$-units submodule of $\overline{\mathbb{Q}}^{\times}$; and let $v$ be a height-one prime of $\mathcal{O}_L$ containing some prime in $S$. Then there is $t \in$ `AddCircle (1 : ℚ)` $= \mathbb{Q}/\mathbb{Z}$ with `HasBrauerLocalInvAt p S L a v t`, that is: there exist a finite extension $F \supseteq L$ inside $\overline{\mathbb{Q}}$, normal over $\mathbb{Q}$ and unramified outside $S$, with `levelField L F` Galois over $L$; a homomorphism $\iota$ from $\mathrm{Gal}(\mathrm{levelField}\,L\,F/L)$ to the quotient of the fixing subgroup of $L$ by the preimage of that of $F$, compatible with `levelGal`; an isomorphism $\varphi$ of representations from the restriction along $\iota$ of the $F$-invariants quotient of `sUnitsMaxRep S L` onto the $S$-units representation [`NumberField.SUnits.sUnitsRep`](def/NumberField_SUnitsModule.html#L52), compatible with the underlying values in $\overline{\mathbb{Q}}$; an idèle Galois descent datum $D$ for $\mathrm{levelField}\,L\,F$ over $L$ together with a multiplicative action on the adelic units given by $D$, and a representation morphism $j$ realising the principal-idèle map; and a $2$-cocycle $f$ whose class inflates to $a$ under `continuousH2SrInflation`, such that the image of the class of $f$ under the map induced in degree $2$ by $\iota$ and by $\varphi$ followed by $j$ has local invariant $t$ at $v$ in the sense of [`NumberField.IdeleLocalInv.HasLocalInv`](def/NumberField_IdeleLocalInvariant.html#L14).
--
--   This is the existence half of the theory of local invariants for the $p$-primary part of the $S$-ramified second cohomology of the $S$-units of $L$, that is, for the $p$-primary Brauer group of $\mathcal{O}_{L,S}$: every such class, at every place of $L$ above $S$, admits a presentation over a finite Galois level together with an idèlic reading, and hence a local invariant in $\mathbb{Q}/\mathbb{Z}$. It is used by [`NumberField.LevelArith.exists_isBrauerLocalInv`](thm.html#NumberField.LevelArith.exists_isBrauerLocalInv) and by [`NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv`](thm.html#NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv), which together turn the relation `HasBrauerLocalInvAt` into a well-defined invariant and record its Galois equivariance.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_hasBrauerLocalInvAt.lean

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
open CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits ExtCitation
open groupCohomology
open NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.exists_hasBrauerLocalInvAt
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) (v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) :
    ∃ t : AddCircle (1 : ℚ), HasBrauerLocalInvAt p S L a v t := by sorry
