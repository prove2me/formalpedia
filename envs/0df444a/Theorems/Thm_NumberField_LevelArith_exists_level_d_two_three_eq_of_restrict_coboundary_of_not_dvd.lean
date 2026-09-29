-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_d_two_three_eq_of_restrict_coboundary_of_not_dvd
-- name    : NumberField.LevelArith.exists_level_d_two_three_eq_of_restrict_coboundary_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/9cc47964-ea92-57ef-bf38-af10e0ae025b
-- title:
--   Prime-to-p descent of degree-3 S-unit coboundaries
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes, and let $L \le L' \le F$ be intermediate fields of $\bar{\mathbb Q}/\mathbb Q$ (the inclusions $L\le L'$, $L'\le F$ and $L\le F$ being given), each finite-dimensional over $\mathbb Q$, with $F$ normal over $\mathbb Q$ and unramified outside $S$ in the sense that $F/\mathbb Q$ is finite and, for every prime $q\notin S$ and every valuation subring $A$ of $\bar{\mathbb Q}$ in which $q$ is a nonunit, the image in $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ lies in the fixing subgroup of $F$. Assume $p$ does not divide $[\,L' : L\,]$, i.e. the rank over $L$ of $L'$ viewed as an extension of $L$ via `levelField`. Write $U_F^L$ for the fixing subgroup of $F$ pulled back to $\Gamma_L := \mathrm{Gal}(\bar{\mathbb Q}/L)$, and let $M_L$ denote the $U_F^L$-invariants of the $\mathbb Z$-representation of $\Gamma_L$ on the additive group of the subgroup `sUnitsMaxStable S L` of $\bar{\mathbb Q}^\times$, regarded as a representation of $\Gamma_L/U_F^L$; similarly for $L'$. Let $f$ be an inhomogeneous $3$-cochain of $\Gamma_L/U_F^L$ with values in $M_L$ which is a cocycle, $\mathrm{d}^{3,4}f = 0$, and suppose a $2$-cochain $b_0$ satisfies $\mathrm{d}^{2,3}b_0 = p^k\!\cdot\! f$ for some $k\in\mathbb N$. Let $f'$ be a $3$-cochain for $L'$ at level $F$ which restricts $f$, in the sense that whenever $g : \mathrm{Fin}\,3 \to \Gamma_{L'}$ and $g_0 : \mathrm{Fin}\,3 \to \Gamma_L$ have componentwise equal underlying automorphisms of $\bar{\mathbb Q}$, the underlying elements of $\bar{\mathbb Q}$ of $f'(\bar g)$ and $f(\bar g_0)$ coincide. Assume finally that $f'$ becomes a coboundary at a deeper level: there are an intermediate field $F' \supseteq F$, unramified outside $S$ and Galois over $\mathbb Q$, and a $2$-cochain $b'$ for $L'$ at level $F'$ with $f'(\bar g) = (\mathrm{d}^{2,3}b')(\bar g)$ in the $S$-unit module for all $g : \mathrm{Fin}\,3\to\Gamma_{L'}$. The conclusion is the same statement for $f$ over $L$: there exist an intermediate field $F' \supseteq F$, unramified outside $S$ and Galois over $\mathbb Q$, and a $2$-cochain $b$ of $\Gamma_L/U_{F'}^L$ with values in the $U_{F'}^L$-invariants, such that $f(\bar g) = (\mathrm{d}^{2,3}b)(\bar g)$ as elements of the $S$-unit module for every $g : \mathrm{Fin}\,3 \to \Gamma_L$.
--
--   This is the prime-to-$p$ descent step in degree $3$ for cochains of $S$-unit modules along the tower of finite levels: restriction–corestriction multiplies by $[L':L]$ at cochain level, and together with the relation $\mathrm{d} b_0 = p^k f$ a Bézout argument converts vanishing of the class of $f'$ over $L'$ into vanishing of that of $f$ over $L$ at a possibly deeper finite level. It is used in the analysis of $S$-idele and $p$-group layer classes, being cited by [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup) and [`NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul`](thm.html#NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_d_two_three_eq_of_restrict_coboundary_of_not_dvd.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.exists_level_d_two_three_eq_of_restrict_coboundary_of_not_dvd
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L'] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (hcop : ¬ p ∣ Module.finrank ↥L ↥(levelField L L' hLL'))
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hf : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0)
    (k : ℕ) (b₀ : (Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hk : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f)
    (f' : (Fin 3 → (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (hff' : ∀ (g : Fin 3 → ↥L'.fixingSubgroup) (g₀ : Fin 3 → ↥L.fixingSubgroup),
        (∀ i, ((g₀ i : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = ((g i : ↥L'.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
        ((sUnitsMaxRep.val S L' ((f' (fun i => (g i : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g₀ i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (hcob : ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F') (_ : F ≤ F')
      (b' : (Fin 2 → (↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L'.fixingSubgroup,
        ((f' (fun i => (g i : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : sUnitsMaxRep S L')
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))).d 2 3).hom b' (fun i => (g i : (↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : sUnitsMaxRep S L')) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F') (_ : F ≤ F')
      (b : (Fin 2 → (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b (fun i => (g i : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by sorry
