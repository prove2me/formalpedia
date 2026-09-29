-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_layer_presentation_and_pow_smul_eq_zero
-- name    : NumberField.LevelArith.exists_layer_presentation_and_pow_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/f085f664-19ad-55c5-9dda-b6ef29e6de1c
-- title:
--   One layer presentation for a p-primary H²_S class
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes, and let $L$ be a finite-dimensional intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is unramified outside $S$, in the sense that $L/\mathbb{Q}$ is finite and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup $\Gamma_L$ of $L$. Let $a$ be an element of the $p$-power torsion submodule (torsion for the powers of $(p : \mathbb{Z})$) of `continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)`, the quotient of the level $S$-cocycle submodule `levelCocyclesSr₂` by the level coboundaries, for the representation of $\Gamma_L$ on the submodule `sUnitsMaxSubmodule S L` of `Additive (AlgebraicClosure ℚ)ˣ`. Then there exist an intermediate field $F \supseteq L$, finite-dimensional and normal over $\mathbb{Q}$ and unramified outside $S$ (witness `hF`), such that the level field $\mathcal{L} =$ `levelField L F hLF` (that is, $F$ with scalars extended to $L$) is Galois over $L$, together with the following data. Writing $H$ for the preimage of $\Gamma_F$ in $\Gamma_L$: a monoid homomorphism $\iota : \mathrm{Gal}(\mathcal{L}/L) \to \Gamma_L/H$ with $\iota(\mathrm{levelGal}\,g)$ the class of $g$ for all $g \in \Gamma_L$; a morphism $\varphi$ of representations from the restriction along $\iota$ of `(sUnitsMaxRep S L).quotientToInvariants H` (the action of $\Gamma_L/H$ on the $H$-invariants) to the $S$-units representation [`NumberField.SUnits.sUnitsRep L 𝓛 (placesOverPrimesFinset L S)`](def/NumberField_SUnitsModule.html#L52), whose underlying map is bijective and which is value-pinned, i.e. the image in $\overline{\mathbb{Q}}$ of the $S$-unit value of $\varphi(x)$ equals `sUnitsMaxRep.val S L` of the underlying element of $x$; an idèle Galois descent datum $D$ for $\mathcal{L}/L$, namely a monoid homomorphism from $\mathrm{Gal}(\mathcal{L}/L)$ to the ring automorphisms of `AdeleRing (𝓞 𝓛) 𝓛` which is continuous for each $g$ and compatible with $g$ on principal adèles; a multiplicative distributive action of $\mathrm{Gal}(\mathcal{L}/L)$ on the adèle units agreeing with `D.unitsAct`; a morphism $j$ from the $S$-units representation to `Rep.ofMulDistribMulAction` on the adèle units sending $y$ to the principal idèle attached to the value of $y$; and finally a $2$-cocycle $f$ of `(sUnitsMaxRep S L).quotientToInvariants H` and a natural number $k$ such that $a$ is the image of the class $H^2\pi(f)$ under the inflation map `continuousH2SrInflation` for $F$, and $(p^k : \mathbb{Z}) \cdot H^2\pi(f) = 0$.
--
--   This packages, for a single $p$-primary class in the continuous $S$-ramified $H^2$ of the $S$-units of the maximal extension unramified outside $S$, one finite Galois layer $F/L$ carrying simultaneously the identification of the layer invariants with the $S$-units of the layer, a Galois descent datum on the layer's idèles, the principal-idèle map, and a layer cocycle inflating to the class. Producing the presentation once for the class is what allows the local invariants at the various places of $L$ to be compared and summed; it is used in the proofs of [`NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv) and [`NumberField.LevelArith.injective_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.injective_of_isBrauerLocalInv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_layer_presentation_and_pow_smul_eq_zero.lean

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
open NumberField
open M4aHerbrand
open scoped NumberField

theorem NumberField.LevelArith.exists_layer_presentation_and_pow_smul_eq_zero
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) :
    ∃
      (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (_ : FiniteDimensional ℚ ↥F) (_ : Normal ℚ ↥F)
      (_ : IsGalois ↥L ↥(levelField L F hLF)) (hF : F.IsUnramifiedOutside S)

      (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
      (_ : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
      (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
        NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
      (_ : Function.Bijective φ.hom)
      (_ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

      (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
      (_ : MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
      (hactI : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • y = D.unitsAct g y)
      (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶
        Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
      (_ : ∀ y, Additive.toMul (j.hom y) =
        Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))
          (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))

      (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) (k : ℕ),
      (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) =
          continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f) ∧
        (p ^ k : ℤ) • H2π _ f = 0 := by sorry
