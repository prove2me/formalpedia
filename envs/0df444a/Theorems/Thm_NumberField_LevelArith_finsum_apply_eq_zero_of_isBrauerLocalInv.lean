-- Prove2me | Theorems.Thm_NumberField_LevelArith_finsum_apply_eq_zero_of_isBrauerLocalInv
-- name    : NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/e35fdec9-64d1-5924-9773-c53a55895a63
-- title:
--   Reciprocity for p-primary S-ramified classes over L
-- statement:
--   Let $p$ be a prime and $S$ a finite set of rational primes containing $p$, and let $L$ be a finite intermediate field of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ which is unramified outside $S$ in the sense that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$; assume moreover that if $p = 2$ then $L$ contains an element $i$ with $i^2 = -1$. Let $M$ denote the $p$-power torsion submodule, i.e. the torsion with respect to the powers of $p$ in $\mathbb{Z}$, of the $S$-ramified continuous degree-two cohomology `continuousH2Sr` of the representation `sUnitsMaxRep S L` of the fixing subgroup of $L$ on the maximal $S$-unit submodule of $\overline{\mathbb{Q}}^{\times}$, taken along the inclusion of that fixing subgroup. Let $\mathrm{inv}$ be any $\mathbb{Z}$-linear map from $M$ to the functions on the set of height-one primes $w$ of $\mathcal{O}_L$ containing some rational prime of $S$, with values in $\mathbb{Q}/\mathbb{Z}$ (written `AddCircle (1 : ℚ)`), satisfying `IsBrauerLocalInv p S L inv`: whenever a class $a \in M$ is the inflation, along a finite layer $F \supseteq L$ normal over $\mathbb{Q}$ and unramified outside $S$ equipped with the comparison data (an identification $\iota$ of the relative Galois group with the quotient of fixing subgroups, an isomorphism $\varphi$ of the invariants of `sUnitsMaxRep` with the $S$-unit representation compatible with values, a Galois descent datum $D$ for the adèles with its induced action, and the map $j$ sending $S$-units to principal idèles), of the class of a $2$-cocycle $f$, and $t$ is a local invariant at $v$ of the image of that class in the degree-two cohomology of the idèle units, then $\mathrm{inv}(a)(v) = t$. Then for every $a \in M$ the sum of $\mathrm{inv}(a)(v)$ over all such places $v$ is $0$ in $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the reciprocity law for the $p$-primary part of the Brauer group of $\mathcal{O}_{L,S}$: the local invariants of a global $S$-ramified class at the places above $S$ sum to zero. It is used in the construction of the natural local-invariant map on the $p$-primary $S$-ramified cohomology of the maximal $S$-units, [`groupCohomology.exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax`](thm.html#groupCohomology.exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax), which feeds the arithmetic of levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_finsum_apply_eq_zero_of_isBrauerLocalInv.lean

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

theorem NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
        →ₗ[ℤ] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ)))
    (hinv : IsBrauerLocalInv p S L inv) (a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) :
    ∑ᶠ v, inv a v = 0 := by sorry
