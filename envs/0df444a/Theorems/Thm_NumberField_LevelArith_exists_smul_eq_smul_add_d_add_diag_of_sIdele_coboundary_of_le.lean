-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le
-- name    : NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/691c4007-d13f-56b8-a36c-178bee848080
-- title:
--   Torsion transfer of S-idèle cochains along a level tower
-- statement:
--   Fix a finite set $S$ of rational primes and intermediate fields $L\le F$ and $L\le L_1\le F_1$ of $\overline{\mathbb Q}/\mathbb Q$ with $F\le F_1$, all finite over $\mathbb Q$, with $F$ and $F_1$ normal over $\mathbb Q$, and with $K:=\mathrm{levelField}(L,F)$ Galois over $L$ and $K_1:=\mathrm{levelField}(L_1,F_1)$ Galois over $L_1$ ($\mathrm{levelField}$ being the extension of scalars of the larger field to a field over the smaller one). Put $G:=\mathrm{Gal}(K/L)$, $G_1:=\mathrm{Gal}(K_1/L_1)$, and let $n\in\mathbb N$ be divisible by the cardinality of the quotient of the fixing subgroup of $L$ by that of $F$. Write $J$, resp. $J_1$, for the $\mathbb Z[G]$-, resp. $\mathbb Z[G_1]$-module obtained as the product, over the places of $K$ (finite and infinite) above the primes of $\mathcal O_L$ lying over $S$, of the coinduced modules of local units, $U$, $U_1$ for the corresponding $S$-unit submodules of $K^\times$, $K_1^\times$ (written additively), and $\mathrm{diag}$ for the componentwise diagonal maps $U\to J$, $U_1\to J_1$. Assume given $f_1\colon G^3\to U$ and a $2$-cochain $c$ of $J$ with $d c=\mathrm{diag}\circ f_1$ in the inhomogeneous cochain complex, a map $f_1'\colon G_1^3\to U_1$ whose values in $\overline{\mathbb Q}$ agree with those of $f_1$ in the sense that for all triples $g$ in the fixing subgroup of $L_1$ and $g_0$ in that of $L$ with componentwise equal underlying automorphisms of $\overline{\mathbb Q}$ one has $f_1'(\mathrm{levelGal}(g))=f_1(\mathrm{levelGal}(g_0))$ as elements of $\overline{\mathbb Q}$, and an arbitrary $2$-cochain $c_1$ of $J_1$ with $d c_1=\mathrm{diag}\circ f_1'$. Then there exist a $2$-cochain $\zeta$ of $J_1$ with $d\zeta=0$, a $1$-cochain $\omega$ of $J_1$ and a $2$-cochain $e$ with values in $U_1$ such that $n\cdot c_1=n\cdot\zeta+d\omega+\mathrm{diag}\circ e$.
--
--   The assertion is that the class of $c_1$ in $H^2(G_1,J_1/U_1)$ becomes $n$-torsion modulo the image of the $S$-idèles, where $n$ is a multiple of the order of the Galois group at the lower level of the tower: corestriction–restriction torsion at level $(L,F)$ is transported along the base change of $S$-idèles to level $(L_1,F_1)$. It feeds the degree-$2$ bookkeeping behind the vanishing of the $p$-part of $H^3$ for $S$-units, being used by [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le.lean

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

theorem NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le
    (S : Finset Nat.Primes)
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)]
    (L₁ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F₁ : L₁ ≤ F₁) (hFF₁ : F ≤ F₁)
    [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F₁] [Normal ℚ ↥F₁] [IsGalois ↥L₁ ↥(levelField L₁ F₁ hL₁F₁)]
    (n : ℕ) (hn : Nat.card (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) ∣ n)

    (f₁ : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (c : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hc : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom c = fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (f₁ g))

    (f₁' : (Fin 3 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SUnits.sUnitsRep ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)))
    (hff' : ∀ (g : Fin 3 → ↥L₁.fixingSubgroup) (g₀ : Fin 3 → ↥L.fixingSubgroup),
      (∀ i, ((g₀ i : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = ((g i : ↥L₁.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((NumberField.SUnits.val ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S) (f₁' (fun i => levelGal L₁ F₁ hL₁F₁ (g i))) : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ)
        = ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (f₁ (fun i => levelGal L F hLF (g₀ i))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ))
    (c₁ : (Fin 2 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)))
    (hc₁ : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))).d 2 3).hom c₁ = fun g => (NumberField.SIdele.diag ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)).hom (f₁' g)) :
    ∃ (ζ : (Fin 2 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))) (ω : (Fin 1 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))) (e : (Fin 2 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SUnits.sUnitsRep ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))),
      ((inhomogeneousCochains (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))).d 2 3).hom ζ = 0 ∧
      (n : ℤ) • c₁ = (n : ℤ) • ζ + ((inhomogeneousCochains (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))).d 1 2).hom ω + fun g => (NumberField.SIdele.diag ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)).hom (e g) := by sorry
