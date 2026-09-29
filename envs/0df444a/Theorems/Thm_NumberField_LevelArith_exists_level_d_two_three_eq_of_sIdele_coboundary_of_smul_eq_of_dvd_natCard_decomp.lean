-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp
-- name    : NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/6e9146be-8f28-58b1-9640-35d8e8d5110d
-- title:
--   Depth splitting of a 3-cocycle of S-units
-- statement:
--   Fix a prime $p$ and a finite set $S$ of primes with $p \in S$. Let $L \subseteq \overline{\mathbb Q}$ be a finite intermediate field that is unramified outside $S$ (for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ lies in the fixing subgroup of $L$), and assume $L$ contains a square root of $-1$ when $p=2$. Let $F \supseteq L$ be a finite intermediate field, normal over $\mathbb Q$ and unramified outside $S$, with $K :=$ `levelField L F hLF` $= F$ viewed over $L$ Galois over $L$, and assume the quotient $\Gamma_L/U_F$ of the fixing subgroup of $L$ by the preimage of the fixing subgroup of $F$ is a $p$-group. Let $\iota : \mathrm{Gal}(K/L) \to \Gamma_L/U_F$ be a homomorphism compatible with `levelGal` and the quotient map, and let $\varphi$ be a morphism of representations, bijective on underlying modules, from the $\iota$-restriction of the $U_F$-invariants of the big $S$-unit module `sUnitsMaxRep S L` (a $\mathbb Z[\Gamma_L]$-submodule of $\mathrm{Additive}\,\overline{\mathbb Q}^\times$) to the $S$-units representation of $K/L$ for the places of $L$ above $S$, such that $\varphi$ preserves values in $\overline{\mathbb Q}$. Let $f$ be a $3$-cochain of $\Gamma_L/U_F$ valued in those invariants with $d f = 0$, let $f_1$ be a $3$-cochain of $\mathrm{Gal}(K/L)$ valued in the $S$-units representation whose values in $\overline{\mathbb Q}$ agree with those of $f$ along `levelGal`, and let $c$ be a $2$-cochain valued in the $S$-idèle module of $K/L$ with $d c = \mathrm{diag} \circ f_1$. Assume further that for some $n \in \mathbb N$ there are a $2$-cocycle $\zeta$ and a $1$-cochain $\omega$ of the $S$-idèle module and a $2$-cochain $e$ of the $S$-units representation with $n \cdot c = n \cdot \zeta + d\omega + \mathrm{diag} \circ e$, and that $n$ divides the order of the decomposition group in $\mathrm{Gal}(K/L)$ of the chosen place of $K$ above some finite place $v_0$ of $L$ lying over $S$. Then there is an intermediate field $F' \supseteq F$, unramified outside $S$ and Galois over $\mathbb Q$, together with a $2$-cochain $b$ of $\Gamma_L/U_{F'}$ valued in the $U_{F'}$-invariants of `sUnitsMaxRep S L`, such that for all $g : \mathrm{Fin}\ 3 \to \Gamma_L$ the value of $f$ at the image of $g$ in $\Gamma_L/U_F$ coincides, as an element of `sUnitsMaxRep S L`, with the value of $d b$ at the image of $g$ in $\Gamma_L/U_{F'}$.
--
--   This is the inductive core of the statement that the $p$-part of $H^3(G_{L,S}, E_S)$ vanishes: a degree-$3$ $S$-unit cocycle whose transport to the $S$-idèles is a coboundary is split after passing to a deeper finite Galois level, provided the torsion relation (T) and the local-degree divisibility (D) are available. It is cited by [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup), which supplies (T) and (D) from a Sylow-type choice of level and of place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp.lean

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain
open M4aHerbrand
open NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφ : Function.Bijective φ.hom)
    (hφval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hf : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0)
    (f₁ : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hff₁ : ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (f₁ (fun i => levelGal L F hLF (g i))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (c : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hc : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom c = fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (f₁ g))

    (n : ℕ) (ζ : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hζ : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom ζ = 0)
    (ω : (Fin 1 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (e : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hT : (n : ℤ) • c = (n : ℤ) • ζ + ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 1 2).hom ω + fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (e g))

    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L)) (hv₀ : v₀ ∈ placesOverPrimesFinset ↥L S)
    (hD : n ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v₀))) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F') (_ : F ≤ F')
      (b : (Fin 2 → (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b (fun i => (g i : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by sorry
