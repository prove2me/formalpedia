-- Prove2me | Theorems.Thm_NumberField_LevelArith_continuousH2SrInflation_H2pi_eq_zero_of_restrict_coboundary_of_not_dvd
-- name    : NumberField.LevelArith.continuousH2SrInflation_H2pi_eq_zero_of_restrict_coboundary_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/70c83882-b076-55a4-aa0a-6e7a995de45c
-- title:
--   Inflated p-primary class vanishes after prime-to-p restriction
-- statement:
--   Let $p$ be a prime, $S$ a finite set of rational primes, and $L \le L' \le F$ intermediate fields of $\overline{\mathbb{Q}}/\mathbb{Q}$ (the inclusions $L \le L'$, $L' \le F$, $L \le F$ being given), each finite over $\mathbb{Q}$, with $F$ normal over $\mathbb{Q}$ and satisfying `IsUnramifiedOutside S`: for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$, viewed inside $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$, fixes $F$ pointwise. Assume $p \nmid [L':L]$, the degree being taken as the rank of $L'$ as a module over $L$. Write $M_L =$ `sUnitsMaxRep S L` for the $\mathbb{Z}[\mathrm{Gal}(\overline{\mathbb{Q}}/L)]$-module given by the subgroup `sUnitsMaxStable S L` of $\overline{\mathbb{Q}}^\times$ written additively, and likewise $M_{L'}$. Let $f$ be an inhomogeneous $2$-cocycle of $\mathrm{Gal}(\overline{\mathbb{Q}}/L)/(\mathrm{Gal}(\overline{\mathbb{Q}}/F)\cap\mathrm{Gal}(\overline{\mathbb{Q}}/L))$ with values in the $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$-invariants of $M_L$, whose class satisfies $p^k\,[f] = 0$ for some $k$, and let $f'$ be such a cocycle for $L'$ which agrees with $f$ on pairs of elements with the same underlying automorphisms of $\overline{\mathbb{Q}}$, i.e. $f'$ is the restriction of $f$. Assume further that there are an intermediate field $F' \supseteq F$ unramified outside $S$ and Galois over $\mathbb{Q}$ and a function $y$ on $\mathrm{Gal}(\overline{\mathbb{Q}}/L')/(\mathrm{Gal}(\overline{\mathbb{Q}}/F')\cap\mathrm{Gal}(\overline{\mathbb{Q}}/L'))$ with values in the $\mathrm{Gal}(\overline{\mathbb{Q}}/F')$-invariants of $M_{L'}$ such that $f'(g,h) = \rho(g)y(h) - y(gh) + y(g)$ for all $g,h$; that is, the inflation of $f'$ to level $F'$ is a coboundary. Then the image of $[f]$ under `continuousH2SrInflation` for $\mathrm{Gal}(\overline{\mathbb{Q}}/L)$, $S$ and $M_L$ at level $F$ — the inflation into the quotient of level-$S$ $2$-cocycles by level-$S$ $2$-coboundaries — is zero.
--
--   This is the prime-to-$p$ descent step in the computation of the $S$-ramified second cohomology of the maximal $S$-units module: a $p$-power-torsion class over $L$ whose restriction to $L'$ capitulates at some deeper $S$-ramified Galois level dies already over $L$, because $[L':L]$ is prime to $p$ and restriction followed by corestriction is multiplication by the index. It is used in [`NumberField.LevelArith.continuousH2SrInflation_H2pi_eq_zero_of_map_principalIdele_eq_zero_of_pow_smul_eq_zero`](thm.html#NumberField.LevelArith.continuousH2SrInflation_H2pi_eq_zero_of_map_principalIdele_eq_zero_of_pow_smul_eq_zero), and rests on the level-by-level criterion [`groupCohomology.continuousH2SrInflation_H2pi_eq_zero_iff`](thm.html#groupCohomology.continuousH2SrInflation_H2pi_eq_zero_iff) together with [`groupCohomology.eq_zero_of_map_res_two_eq_zero_of_coprime`](thm.html#groupCohomology.eq_zero_of_map_res_two_eq_zero_of_coprime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_continuousH2SrInflation_H2pi_eq_zero_of_restrict_coboundary_of_not_dvd.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.continuousH2SrInflation_H2pi_eq_zero_of_restrict_coboundary_of_not_dvd
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L'] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (hcop : ¬ p ∣ Module.finrank ↥L ↥(levelField L L' hLL'))
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (k : ℕ) (hk : (p ^ k : ℤ) • (H2π _ f) = 0)
    (f' : cocycles₂ ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (hff' : ∀ (g h : ↥L'.fixingSubgroup) (g₀ h₀ : ↥L.fixingSubgroup),
      ((g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((h₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((sUnitsMaxRep.val S L' ((f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L ((f ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (hcob : ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ F') (_ : F ≤ F')
      (y : (↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype) →
        (sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype)),
      ∀ g h : ↥L'.fixingSubgroup,
        ((f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L')
          = (sUnitsMaxRep S L').ρ g (y (h : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))
            - (y ((g * h : ↥L'.fixingSubgroup) : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype) : sUnitsMaxRep S L')
            + y (g : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype)) :
    continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f) = 0 := by sorry
