-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d
-- name    : NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/6b4bb601-f6f1-51f5-b671-f2aa4439cc0c
-- title:
--   Capitulation step: idèlic 2-cochain gives deeper S-unit coboundary
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes with $p \in S$. Let $L \subseteq F$ be subfields of $\overline{\mathbb Q}$, both finite over $\mathbb Q$, with $F$ normal over $\mathbb Q$, let $K = \mathrm{levelField}\,L\,F$ be $F$ viewed as an extension of $L$, assumed Galois over $L$, and write $G = \mathrm{Gal}(K/L)$. Assume $F$ is unramified outside $S$ (it is finite over $\mathbb Q$ and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$ lies in the fixing subgroup of $F$), and that the quotient of the fixing subgroup of $L$ by that of $F$ is a $p$-group. Let $D$ be an idèle Galois descent datum for $\mathcal O_K \subseteq K$ over $L$, that is, a monoid homomorphism from $G$ to the ring automorphisms of the adèle ring of $K$ which is continuous and compatible with $\mathrm{algebraMap}$ along the Galois action on $K$; the multiplicative $G$-actions on the adèlic units and on the idèle class group $C_K = (\mathbb A_K)^\times / K^\times$ are assumed to be those given by $D$, and $\pi$ is the morphism of $\mathbb Z$-linear $G$-representations induced by the quotient map. Let $\Phi$ be an injective additive map from the $S$-idèle module $\mathrm{SIdele.obj}\,L\,K$ (the product over the places of $L$ in $\mathrm{placesOverPrimesFinset}\,L\,S$ and the remaining places of the coinduced local unit, respectively local integral unit, representations) into the additive group of $(\mathbb A_K)^\times$, whose range is exactly the group of unit idèles which, together with their inverses, are integral at every finite place of $K$ not lying over $S$, which is equivariant for $D$'s action, and which sends the diagonal image of an $S$-unit to the corresponding principal idèle. Finally let $f_1 \colon G^3 \to \mathcal O_{K,S}^\times$ and $u \colon G^2 \to \mathrm{SIdele.obj}\,L\,K$ satisfy $du = \mathrm{diag} \circ f_1$ in inhomogeneous cochains, let $\xi \colon G^2 \to (\mathbb A_K)^\times$ be a cocycle ($d\xi = 0$) all of whose values are unit idèles integral outside $S$, and let $\nu \colon G^1 \to C_K$ be such that $\pi(\Phi(u(g))) = \pi(\xi(g)) + (d\nu)(g)$ for all $g \in G^2$. The conclusion asserts the existence of an intermediate field $F_2 \supseteq F$, finite over $\mathbb Q$, unramified outside $S$ in the above sense and Galois over $\mathbb Q$, together with a $2$-cochain $e_2$ on $\mathrm{Gal}(\mathrm{levelField}\,L\,F_2 / L)$ with values in the $S$-units of $\mathrm{levelField}\,L\,F_2$, such that for all $g_2 \in \mathrm{Gal}(\mathrm{levelField}\,L\,F_2/L)^3$ and all $g_0$ in the cube of the fixing subgroup of $L$ with $g_2(i)$ acting on $\mathrm{levelField}\,L\,F_2$ as $g_0(i)$ does on $\overline{\mathbb Q}$ for each $i$, the value of $(d e_2)(g_2)$ equals the value of $f_1$ at the restrictions $\mathrm{levelGal}\,L\,F(g_0(i))$, as elements of $\overline{\mathbb Q}$.
--
--   This is the capitulation step in the level-raising argument for $S$-unit cocycles: once the $S$-idèle $2$-cochain $u$ bounding $f_1$ is known to agree, in $H^2(G, C_K)$, with a cocycle of idèles integral outside $S$, the residual obstruction to $f_1$ being a coboundary of $S$-units is a $1$-cocycle with values in the $S$-class group, and it is killed after passing to a larger finite Galois field $F_2$ unramified outside $S$. It is used by [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d.lean

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
open CategoryTheory groupCohomology ExtCitation IsDedekindDomain NumberField.LevelArith
open NumberField
open M4aHerbrand
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))

    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))]
    (hact : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (x : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))), g • x = D.classAct g x)

    (π : (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))
    (hπ : ∀ x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))

    (Φ : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) →+ Additive (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hΦinj : Function.Injective Φ)
    (hΦrange : Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}).toAddSubgroup)
    (hΦρ : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))), Φ ((NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ g y) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ y))))
    (hΦdiag : ∀ x : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), Φ ((NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom x) =
      Additive.ofMul (Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x)))

    (f₁ : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (u : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hu : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom u = fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (f₁ g))

    (ξ : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ))
    (hξ : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 2 3).hom ξ = 0)
    (hξS : ∀ g : Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), (Additive.toMul (ξ g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)})
    (ν : (Fin 1 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))
    (hkill : ∀ g : Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), π.hom (Φ (u g)) = π.hom (ξ g) + ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))).d 1 2).hom ν g) :
    ∃ (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hfd : FiniteDimensional ℚ ↥F₂) (_ : F₂.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F₂)
      (hFF₂ : F ≤ F₂),
      haveI := hfd
      ∃ e₂ : (Fin 2 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂)))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)),
        ∀ (g₂ : Fin 3 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂)))) (g₀ : Fin 3 → ↥L.fixingSubgroup),
          (∀ (i : Fin 3) (x : ↥(levelField L F₂ (hLF.trans hFF₂))), (((g₂ i) x : ↥(levelField L F₂ (hLF.trans hFF₂))) : AlgebraicClosure ℚ) = ((g₀ i : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ)) →
          ((NumberField.SUnits.val ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S) (((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom e₂ (fun i => g₂ i)) : ↥(levelField L F₂ (hLF.trans hFF₂))) : AlgebraicClosure ℚ)
            = ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (f₁ (fun i => levelGal L F hLF (g₀ i))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) := by sorry
