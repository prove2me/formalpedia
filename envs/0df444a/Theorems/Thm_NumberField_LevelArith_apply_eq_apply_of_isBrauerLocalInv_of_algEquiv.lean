-- Prove2me | Theorems.Thm_NumberField_LevelArith_apply_eq_apply_of_isBrauerLocalInv_of_algEquiv
-- name    : NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/772b6163-d4ba-5d83-bd0e-6a15d55729a5
-- title:
--   Naturality of Brauer local invariants under automorphisms of L
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$, and let $L$ be a finite intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$ that is unramified outside $S$, in the sense that for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup $\Gamma_L$ of $L$; assume moreover that $L$ contains a square root of $-1$ when $p=2$. Let $\mathrm{inv}$ be a $\mathbb{Z}$-linear map from the $p$-power torsion submodule of $H^2$ of the level ($S$-ramified) complex for $\Gamma_L$ acting on the $S$-units $E_S\subset\overline{\mathbb{Q}}^{\times}$ — the quotient of the level $2$-cocycles `levelCocyclesSr₂` by the level $2$-coboundaries — to functions from the set of height-one primes of $\mathcal{O}_L$ containing some prime of $S$ to $\mathbb{Q}/\mathbb{Z} =$ `AddCircle 1`, and suppose $\mathrm{inv}$ satisfies `IsBrauerLocalInv p S L`: for every presenting layer $F\supseteq L$ that is finite and normal over $\mathbb{Q}$ and unramified outside $S$, with comparison data (an isomorphism $\iota$ of the relative Galois group with the quotient of $\Gamma_L$, an identification $\varphi$ of the invariants of the $S$-unit representation with the $S$-units of the level field, a Galois descent structure $D$ on the adeles together with the embedding $j$ of $S$-units into idele classes, all compatibilities being summarised here), every $2$-cocycle $f$ whose inflated class is $a$, every place $v$ over $S$ and every $t$, the relation [`NumberField.IdeleLocalInv.HasLocalInv`](def/NumberField_IdeleLocalInvariant.html#L14) for the image of the class of $f$ at $v$ with value $t$ forces $\mathrm{inv}\,a\,v=t$. The assertion is then: for all $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all $\tau\in\mathrm{Aut}_{\mathbb{Q}}(L)$ such that $\sigma$ restricted to $L$ is $\tau$; for all $a,a'$ in the $p$-power torsion part and all level $2$-cocycles $w,w'$ representing $a$ and $a'$ respectively; if for all $s,t,s',t'\in\Gamma_L$ with $\sigma^{-1}s\sigma=s'$ and $\sigma^{-1}t\sigma=t'$ one has $w'(s,t)=\sigma\cdot w(s',t')$ as elements of $\overline{\mathbb{Q}}^{\times}$; then for all places $v,v'$ of $L$ over $S$ with $v'(\tau y)=v(y)$ for all $y\in L$, one has $\mathrm{inv}\,a'\,v'=\mathrm{inv}\,a\,v$.
--
--   This is the functoriality (naturality) of the local invariant maps on the $p$-primary part of the $S$-ramified second cohomology of the $S$-units — the $p$-primary Brauer group of $\mathcal{O}_{L,S}$ — under an automorphism $\tau$ of $L$ induced by an automorphism $\sigma$ of $\overline{\mathbb{Q}}$: conjugating a cocycle by $\sigma$ transports the invariant at $v$ to the invariant at the transported place $v'$. It holds for any map characterised by `IsBrauerLocalInv`, and is the naturality clause of [`groupCohomology.exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax`](thm.html#groupCohomology.exists_natural_localInv_pPrimary_continuousH2Sr_sUnitsMax), which produces such a family of invariant maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_apply_eq_apply_of_isBrauerLocalInv_of_algEquiv.lean

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

theorem NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
        →ₗ[ℤ] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ)))
    (hinv : IsBrauerLocalInv p S L inv) :
    ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L), (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →
        ∀ (a a' : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))))
          (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))),
          (a : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w →
          (a' : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w' →
          (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            sUnitsMaxRep.val S L ((w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s, t)) =
              σ • sUnitsMaxRep.val S L ((w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s', t'))) →
          ∀ (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) →
            inv a' v' = inv a v := by sorry
