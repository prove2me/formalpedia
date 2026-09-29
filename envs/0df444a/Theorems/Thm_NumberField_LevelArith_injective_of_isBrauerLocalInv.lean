-- Prove2me | Theorems.Thm_NumberField_LevelArith_injective_of_isBrauerLocalInv
-- name    : NumberField.LevelArith.injective_of_isBrauerLocalInv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/010142ae-adf5-5f2f-a72e-cd78b1a035a1
-- title:
--   Injectivity of any Brauer local-invariant map on p-primary classes
-- statement:
--   Let $p$ be a prime and $S$ a finite set of rational primes containing $p$, and let $L$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, which is unramified outside $S$ in the sense of [`IntermediateField.IsUnramifiedOutside`](def/GroupCohomology_ContinuousUnramified.html#L16): $L$ is finite over $\mathbb{Q}$ and for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup $\Gamma_L$ of $L$. Assume further that if $p = 2$ then $L$ contains an element $i$ with $i^2 = -1$. Let $\mathrm{inv}$ be a $\mathbb{Z}$-linear map from the $p$-power torsion submodule (torsion with respect to the powers of $p$ in $\mathbb{Z}$) of the $S$-ramified continuous second cohomology `continuousH2Sr` of $\Gamma_L$ acting on the representation `sUnitsMaxRep S L` of maximal $S$-units inside $\overline{\mathbb{Q}}^{\times}$ — the quotient of the module of level $S$-cocycles in degree $2$ by the $S$-coboundaries lying in it — to the module of functions from the set of height-one primes $w$ of $\mathcal{O}_L$ containing some prime of $S$ to $\mathbb{Q}/\mathbb{Z}$, written `AddCircle (1 : ℚ)`. Suppose $\mathrm{inv}$ satisfies `IsBrauerLocalInv p S L`, namely: for every finite normal extension $F$ of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ containing $L$, unramified outside $S$, with $\operatorname{levelField} L F$ Galois over $L$, for every identification $\iota$ of $\operatorname{Gal}(\operatorname{levelField} L F / L)$ with $\Gamma_L/\Gamma_F$ compatible with `levelGal`, every bijective morphism $\varphi$ from the $\Gamma_F$-invariants of `sUnitsMaxRep S L` (restricted along $\iota$) to the representation of $S$-units of the layer respecting the underlying values, every idele Galois descent $D$ for the adele ring of the layer with the assumption that the Galois action on the idele group is the one induced by $D$, every morphism $j$ sending $S$-units to the corresponding principal ideles, every $2$-cocycle $f$ of the invariants representation, every class $a$ in the $p$-power torsion submodule whose underlying class is the inflation `continuousH2SrInflation` of the class of $f$, and every place $v$ over $S$ and $t \in \mathbb{Q}/\mathbb{Z}$: if the image of the class of $f$ under the map in degree $2$ induced by $\iota$ and by $\varphi$ followed by $j$ has local invariant $t$ at $v$ in the sense of [`NumberField.IdeleLocalInv.HasLocalInv`](def/NumberField_IdeleLocalInvariant.html#L14), then $\mathrm{inv}\, a\, v = t$. The conclusion is that $\mathrm{inv}$ is injective.
--
--   This is the Hasse principle (Brauer–Hasse–Noether) for the $p$-primary part of the Brauer group of $\mathcal{O}_{L,S}$, in the form: a $p$-power torsion class in the $S$-ramified $H^2$ of the $S$-units all of whose local invariants at the places above $S$ vanish is itself zero, stated for an arbitrary map satisfying the local-invariant characterisation rather than for a specific construction. It is used in the construction of a natural local-invariant map on the $p$-primary part of `continuousH2Sr` for the maximal $S$-units, which feeds the level arithmetic over $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_injective_of_isBrauerLocalInv.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.injective_of_isBrauerLocalInv
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
        →ₗ[ℤ] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ)))
    (hinv : IsBrauerLocalInv p S L inv) :
    Function.Injective inv := by sorry
