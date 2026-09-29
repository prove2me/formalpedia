-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep
-- name    : NumberField.LevelArith.exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/8a987845-8c9f-55d2-8ed8-d8df2eb4fcb6
-- title:
--   Capitulation at a larger level of S-unit 2-cocycles
-- statement:
--   Fix a natural number $p$ and a finite set $S$ of primes containing a prime equal to $p$, and intermediate fields $L \le F$ of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, both finite over $\mathbb{Q}$, with $F$ normal over $\mathbb{Q}$ and the level field `levelField L F hLF` (that is, $F$ with scalars extended to $L$) normal over $L$. Assume $F$ is unramified outside $S$ in the sense of `IsUnramifiedOutside`: $F$ is finite over $\mathbb{Q}$ and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$, pushed into $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$, lies in the fixing subgroup of $F$. Write $N_F$ for the preimage of $F$'s fixing subgroup in $\Gamma_L := L.\mathrm{fixingSubgroup}$, and assume the quotient $\Gamma_L / N_F$ is a $p$-group. Let $\iota$ be a group homomorphism from $\mathrm{Gal}(\mathrm{levelField}\,L\,F / L)$ to $\Gamma_L/N_F$ with $\iota(\mathrm{levelGal}(g))$ the class of $g$ for all $g \in \Gamma_L$, and let $\varphi$ be a morphism of representations from the restriction along $\iota$ of the $\Gamma_L/N_F$-representation on the $N_F$-invariants of the maximal $S$-unit module `sUnitsMaxRep S L` to the $S$-units `sUnitsRep` of the level field over $L$ for the places `placesOverPrimesFinset L S`, such that the underlying map of $\varphi$ is bijective and preserves the underlying element of $\overline{\mathbb{Q}}$. Let $f$ be a $2$-cocycle of $\Gamma_L/N_F$ with values in the $N_F$-invariants of `sUnitsMaxRep S L`, and suppose that the class of $f$ is sent to $0$ by the degree-$2$ cohomology map induced by $\iota$ and by $\varphi$ followed by the diagonal [`NumberField.SIdele.diag`](def/NumberField_SIdeleModule.html#L91) into the $S$-idèle module. Then there exist an intermediate field $F'$ with $F \le F'$, unramified outside $S$ and Galois over $\mathbb{Q}$, and a function $y$ from $\Gamma_L / N_{F'}$ to the $N_{F'}$-invariants of `sUnitsMaxRep S L`, such that for all $g, h \in \Gamma_L$ one has, as elements of `sUnitsMaxRep S L`, $f(\bar g, \bar h) = \rho(g)\,y(h') - y((gh)') + y(g')$, where bars denote classes modulo $N_F$ and primes classes modulo $N_{F'}$; that is, the inflation of $f$ to the level $F'$ is the coboundary of $y$.
--
--   This is the finite-layer capitulation step: a $2$-cocycle of a $p$-group layer with $S$-unit coefficients whose class dies in the $S$-idèle cohomology becomes a coboundary after passing to a larger finite level, still unramified outside $S$. It is used in the proofs that a class in the continuous $H^2$ of the maximal $S$-unit module vanishes once all its local images vanish, and in the corresponding inflation statement for principal idèles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.lean

import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory NumberField.LevelArith

theorem NumberField.LevelArith.exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep
    (p : ℕ) (S : Finset Nat.Primes) (hpS : ∃ q ∈ S, (q : ℕ) = p)
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (hF : F.IsUnramifiedOutside S)
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →*
      (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hιg : ∀ g : ↥L.fixingSubgroup,
      ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφ : Function.Bijective φ.hom)
    (hφval : ∀ x,
      ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) :
          ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : groupCohomology.cocycles₂
      ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (himg : (groupCohomology.map ι
        (φ ≫ NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) 2)
        (groupCohomology.H2π _ f) = 0) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ F') (_ : F ≤ F')
      (y : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype) →
        (sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      ∀ g h : ↥L.fixingSubgroup,
        ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
              (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
            (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
          = (sUnitsMaxRep S L).ρ g (y (h : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))
            - (y ((g * h : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype) :
                sUnitsMaxRep S L)
            + y (g : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype) := by sorry
