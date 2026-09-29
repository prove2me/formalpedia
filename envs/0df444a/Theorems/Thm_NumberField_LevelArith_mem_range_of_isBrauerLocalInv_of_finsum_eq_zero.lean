-- Prove2me | Theorems.Thm_NumberField_LevelArith_mem_range_of_isBrauerLocalInv_of_finsum_eq_zero
-- name    : NumberField.LevelArith.mem_range_of_isBrauerLocalInv_of_finsum_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/90610406-ed6b-552a-afca-5077e01b1e33
-- title:
--   Realisation of sum-zero p-primary families of local invariants
-- statement:
--   Let $p$ be a prime and $S$ a finite set of rational primes with $p \in S$. Let $L$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, finite over $\mathbb{Q}$, which is unramified outside $S$ in the sense of `IsUnramifiedOutside`: $L$ is finite over $\mathbb{Q}$ and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ having $q$ in its nonunits, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$; if $p = 2$ it is assumed that $L$ contains an element $i$ with $i^2 = -1$. Let $\mathrm{inv}$ be a $\mathbb{Z}$-linear map from the $p$-primary torsion submodule of the $S$-continuous second cohomology `continuousH2Sr` of the fixing subgroup of $L$ with coefficients in the representation `sUnitsMaxRep S L` (the $S$-unit subrepresentation of $\overline{\mathbb{Q}}^{\times}$) to the group of functions from the set of height-one primes $w$ of $\mathcal{O}_L$ containing some rational prime of $S$ to $\mathbb{Q}/\mathbb{Z}$, and suppose $\mathrm{inv}$ satisfies `IsBrauerLocalInv p S L inv`: for every finite normal extension $F/\mathbb{Q}$ containing $L$ and unramified outside $S$ such that the associated level field is Galois over $L$, together with comparison data identifying the Galois group, the $S$-units representation, the idèle Galois descent and the embedding of $S$-units into idèles (these hypotheses are summarised here), and for every $2$-cocycle whose inflated class represents a class $a$ in the $p$-primary part, the value $\mathrm{inv}\,a\,v$ equals any $t \in \mathbb{Q}/\mathbb{Z}$ which is a local invariant at $v$, in the sense of `HasLocalInv`, of the corresponding idèle-class cohomology class. Then every function $f$ from the places of $L$ over $S$ to $\mathbb{Q}/\mathbb{Z}$ all of whose values are annihilated by some power of $p$ and which satisfies $\sum_{w} f(w) = 0$ lies in the range of $\mathrm{inv}$.
--
--   This is the realisation (surjectivity) half of the local-invariant description of the $p$-primary part of the Brauer group of $\mathcal{O}_{L,S}$: the image of $\mathrm{inv}$ contains, hence is, the sum-zero hyperplane in the $p$-primary functions on the places of $L$ above $S$. It feeds the construction of a natural local-invariant map on the $p$-primary $S$-continuous $H^2$ of the maximal $S$-units representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_mem_range_of_isBrauerLocalInv_of_finsum_eq_zero.lean

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
open CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation
open NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.mem_range_of_isBrauerLocalInv_of_finsum_eq_zero
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
        →ₗ[ℤ] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ)))
    (hinv : IsBrauerLocalInv p S L inv)
    (f : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ))
    (hfp : ∀ w, ∃ k : ℕ, (p ^ k : ℤ) • f w = 0) (hfs : ∑ᶠ w, f w = 0) :
    f ∈ LinearMap.range inv := by sorry
