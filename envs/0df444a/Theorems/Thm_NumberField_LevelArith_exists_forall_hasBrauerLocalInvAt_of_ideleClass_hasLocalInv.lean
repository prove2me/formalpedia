-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv
-- name    : NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/cb03c851-0681-57cb-a51b-b3c3c9bdc2d7
-- title:
--   Brauer class with prescribed invariants from an idèle class
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes with $p \in S$ (as the element `pPrime p`). Let $L \subseteq \overline{\mathbb{Q}}$ be a finite intermediate field which is unramified outside $S$, i.e. $L$ is finite over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$ the inertia subgroup of $A$ over $\mathbb{Q}$ is contained in the fixing subgroup of $L$; assume in addition that $L$ contains a square root of $-1$ when $p = 2$. Let $F \supseteq L$ be a further finite intermediate field, normal over $\mathbb{Q}$ and unramified outside $S$, and write $K =$ `levelField L F hLF` for $F$ regarded as an intermediate field over $L$ (so that $K/L$ is Galois). The data concerning $K$ consist of: a descent datum $D$ of type `IdeleGaloisDescent (𝓞 K) L K`; multiplicative actions of $\mathrm{Gal}(K/L)$ on the units of the adèle ring of $K$ and on the idèle class group `IdeleClassGroup (𝓞 K) K`, both pinned by hypotheses `hactI` and `hact` to the actions supplied by $D$; for each finite place $w$ of $K$ a morphism of representations $\mathrm{prG}\,w$ from the restriction of the adèle-unit representation to the subgroup `decomp ↥L ↥K w` attached to $w$ to the units of the $w$-adic completion of $K$, which on elements is the $w$-component map `finPart w`; and a morphism $\pi$ from the adèle-unit representation to the idèle class group representation which on elements is the canonical quotient map. Let $x$ be a class in degree-$2$ group cohomology of $\mathrm{Gal}(K/L)$ with values in the units of the adèle ring of $K$, such that $p^k x = 0$ for some $k$, such that the image of $x$ under restriction to `decomp ↥L ↥K w` followed by $\mathrm{prG}\,w$ vanishes for every finite place $w$ of $K$ whose contraction along $\mathcal{O}_L \to \mathcal{O}_K$ is not one of the places of $L$ above $S$, and such that the image of $x$ under $\pi$ in degree $2$ vanishes. Finally let $t$ assign to each finite place $v$ of $L$ above a prime of $S$ an element of $\mathbb{Q}/\mathbb{Z}$ (written `AddCircle (1 : ℚ)`) with `HasLocalInv ↥L ↥K D hactI x v (t v)` for every such $v$. The conclusion is that there is an element $a$ of the $p$-power torsion submodule `Submodule.torsion' ℤ … (Submonoid.powers (p : ℤ))` of the $S$-level continuous second cohomology `continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)` — the quotient of the $S$-level $2$-cocycles of the fixing subgroup of $L$ acting on `sUnitsMaxRep S L` by the $S$-level coboundaries — such that `HasBrauerLocalInvAt p S L a v (t v)` holds for every place $v$ of $L$ above $S$.
--
--   This is the $S$-unit side of the realisation step: an idèle cohomology class of a finite level $K/L$ which dies in the idèle class group and is supported above $S$ is replaced by a $p$-power torsion class in the $S$-level continuous $H^2$ of the $S$-units of the maximal $S$-ramified extension, with the same prescribed local invariants at the places of $L$ above $S$. In the classical treatment (Tate's and Serre's chapters in Cassels–Fröhlich, or Neukirch–Schmidt–Wingberg) this is the identification of the $p$-part of the Brauer group of $\mathcal{O}_{L,S}$ with classes of given local invariants; here everything is stated at a fixed finite level $K$ with the Galois action on idèles and idèle classes pinned by an explicit descent datum, and the local invariants are recorded by the predicates `HasLocalInv` and `HasBrauerLocalInvAt` rather than by a single invariant map. It is used to prove that a family of $p$-power torsion elements of $\mathbb{Q}/\mathbb{Z}$ indexed by the places above $S$ and summing to zero lies in the range of the Brauer local-invariant map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv.lean

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
open scoped NumberField NumberField.PlaceDecomp
open M4aHerbrand
open IsDedekindDomain

theorem NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • y = D.unitsAct g y)
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))]
    (hact : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (c : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))), g • c = D.classAct g c)
    (prG : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      Rep.res (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) (w.adicCompletion ↥(levelField L F hLF))ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))
    (π : Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))
    (hπ : ∀ y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ, π.hom (Additive.ofMul y) = Additive.ofMul (QuotientGroup.mk y : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))
    (x : groupCohomology (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) 2) (k : ℕ) (hxk : (p ^ k : ℤ) • x = 0)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)), (∀ v ∈ placesOverPrimesFinset ↥L S, w.asIdeal.comap (algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF))) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom x = 0)
    (hπx : (groupCohomology.map (MonoidHom.id (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) π 2).hom x = 0)
    (t : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ))
    (ht : ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)), NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI x v.1 (t v)) :
    ∃ a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))), ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)), HasBrauerLocalInvAt p S L a v (t v) := by sorry
