-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_isBrauerLocalInv
-- name    : NumberField.LevelArith.exists_isBrauerLocalInv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/7490c22f-d99b-556f-a9d2-c72c17f0c0e2
-- title:
--   Existence of a local invariant map on p-primary H²_S
-- statement:
--   Fix a natural number $p$ that is prime, a finite set $S$ of rational primes containing $p$ (as the element `pPrime p` of `Nat.Primes`), and an intermediate field $L$ of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is finite over $\mathbb{Q}$ and satisfies `L.IsUnramifiedOutside S`, i.e. $L/\mathbb{Q}$ is finite and for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$; assume further that if $p = 2$ then $L$ contains an element $i$ with $i^2 = -1$. The assertion is that there exists a $\mathbb{Z}$-linear map $\mathrm{inv}$ from the $p$-power torsion submodule `Submodule.torsion' ℤ _ (Submonoid.powers (p : ℤ))` of `continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)` — the quotient of the $S$-level $2$-cocycles by the $S$-level $2$-coboundaries for the inclusion of $L$'s fixing subgroup into $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, acting on the subrepresentation `sUnitsMaxRep S L` of $\overline{\mathbb{Q}}^{\times}$ cut out by the maximal $S$-unit submodule — to the functions from $\{w \in \mathrm{Spec}^1(\mathcal{O}_L) : (q) \subseteq w \text{ for some } q \in S\}$ to `AddCircle (1 : ℚ)` $= \mathbb{Q}/\mathbb{Z}$, such that `IsBrauerLocalInv p S L inv` holds. The latter says: for every intermediate field $F \supseteq L$ that is finite and normal over $\mathbb{Q}$ and unramified outside $S$, with the relative level field Galois over $L$, and for all presentation data at that level — an isomorphism $\iota$ of the level Galois group with the quotient of fixing subgroups compatible with `levelGal`, a bijective transport $\varphi$ of the $F$-invariant quotient of `sUnitsMaxRep S L` onto the $S$-units representation respecting values, an idèle Galois descent datum $D$ with its unit action, and a map $j$ of the $S$-units representation into the idèle units representation induced by the structure map — together with a $2$-cocycle $f$, an element $a$ of the $p$-primary part whose class is the inflation `continuousH2SrInflation` of the class of $f$, a place $v$ above $S$ and $t \in \mathbb{Q}/\mathbb{Z}$: if the image of the class of $f$ under the map induced by $\iota$ and $\varphi$ followed by $j$ has local invariant $t$ at $v$ in the sense of [`NumberField.IdeleLocalInv.HasLocalInv`](def/NumberField_IdeleLocalInvariant.html#L14) (some $w \mid v$, the $w$-component of the class equals $n$ times the image of a local fundamental class, and $t = n/|D_w|$), then $\mathrm{inv}(a)(v) = t$.
--
--   This is the existence and $\mathbb{Z}$-linearity of Serre's local invariant map on the $p$-primary part of the Brauer group of $\mathcal{O}_{L,S}$, read through finite Galois layers: the invariants $n/|D_w|$ computed layer by layer assemble into a single additive map on $H^2_S$. It is the input to the construction of the natural local-invariant map [`groupCohomology.exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax`](thm.html#groupCohomology.exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax) used in the global duality/level-raising arithmetic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_isBrauerLocalInv.lean

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

theorem NumberField.LevelArith.exists_isBrauerLocalInv
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    ∃ inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
        →ₗ[ℤ] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ)),
      IsBrauerLocalInv p S L inv := by sorry
