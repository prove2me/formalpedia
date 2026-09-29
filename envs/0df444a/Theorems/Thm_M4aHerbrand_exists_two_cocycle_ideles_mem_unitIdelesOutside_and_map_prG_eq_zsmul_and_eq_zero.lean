-- Prove2me | Theorems.Thm_M4aHerbrand_exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero
-- name    : M4aHerbrand.exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/df6cf410-47a3-5df1-8cc0-20ef20db9f98
-- title:
--   A concentrated idèle 2-cocycle above one place
-- statement:
--   Let $K/E$ be a finite Galois extension of number fields with group $G=\mathrm{Gal}(K/E)$, and let $D$ be a descent datum for the adele ring of $K$: a monoid homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_K$, compatible with $\mathrm{algebraMap}$ from $K$ and continuous in each $g$. The given $G$-action on the idèle units $\mathbb{A}_K^\times$ is assumed to be the one induced by $D$ elementwise (`hactI`). For each finite place $w$ of $K$, $\mathrm{prG}\,w$ is a morphism of representations from the restriction of $\mathbb{A}_K^\times$ to the decomposition subgroup $D_w\le G$ (the decomposition subgroup of the valuation subring of $w$) to $(K_w)^\times$, assumed to be given on elements by the $w$-component map `finPart w`. Fix a finite place $v_0$ of $E$, write $w_1$ for the chosen place of $K$ above it, and fix a prime $q$ together with: a finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying actions of $D_{w_1}$ on $L'$ and on $(L')^\times$; a ring isomorphism $\Phi\colon K_{w_1}\to L'$ that is $D_{w_1}$-equivariant, with the action of $D_{w_1}$ fixing $\mathbb{Q}_q$ pointwise and compatible with the action on units; a finite extension $K_0$ of $\mathbb{Q}_q$ which is a base for $L'$ in the sense that $K_0\le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D_{w_1}$; a morphism $\theta$ of $D_{w_1}$-representations $(L')^\times\to (K_{w_1})^\times$ given on elements by $\Phi^{-1}$; and a class $u'\in H^2(D_{w_1},(L')^\times)$ satisfying the predicate `IsLocalFundamentalClass` for $L'$ over $K_0$, i.e. for every unramified overlay datum $(M,H,N_L,N_n,e,\varphi,\pi)$ above $L'$ and every value-preserving comparison morphism $\iota$, the image of $u'$ under the induced map agrees with the inflation of the class of the cyclic carry $2$-cocycle built from the uniformiser $\pi$. Finally let $T$ be a set of finite places of $K$ containing every $w$ whose contraction to $\mathcal{O}_E$ is $v_0$, and let $a\in\mathbb{Z}$. Then there is an inhomogeneous $2$-cochain $\xi\colon G^2\to\mathbb{A}_K^\times$ (written additively) with $d\xi=0$ such that: every value $\xi(g)$ lies in `unitIdelesOutside` for $T$, that is, $\xi(g)$ and its inverse have integral components at every finite place outside $T$; the image of the class of $\xi$ in $H^2$ under restriction to $D_{w_1}$ followed by $\mathrm{prG}\,w_1$ equals $a$ times the image of $u'$ under the map induced by the identity of $D_{w_1}$ and $\theta$; and $\mathrm{finPart}_w(\xi(g))=1$ for every $g$ and every finite place $w$ of $K$ not lying over $v_0$.
--
--   This is the Shapiro-type realisation, at the level of explicit inhomogeneous cochains, of the idèle class concentrated at a single place: its local reading at the chosen place above $v_0$ is $a$ times the local fundamental class and all its other local readings are trivial. It feeds the local–global computation of the invariant of such a class, and is used in [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : (K ≃ₐ[E] K)) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)

    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (v₀ : HeightOneSpectrum (𝓞 E))
    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) L'] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) (↥L')ˣ]
    (Φ : (NumberField.PlaceAbove.above E K v₀).adicCompletion K ≃+* L')
    (hΦ₁ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀))) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (hΦ₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀))) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (hΦ₃ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀))) (y : (NumberField.PlaceAbove.above E K v₀).adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (hK₀ : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) K₀)
    (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ)
    (hθ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v₀).adicCompletion K) = Φ.symm (y : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) (↥L')ˣ))
    (hu' : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) K₀ u')

    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v₀.asIdeal → w ∈ T)
    (a : ℤ) :
    ∃ (ξ : (Fin 2 → (K ≃ₐ[E] K)) → (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))
      (hξ : ((groupCohomology.inhomogeneousCochains (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)).d 2 3).hom ξ = 0),
      (∀ g : Fin 2 → (K ≃ₐ[E] K), Additive.toMul (ξ g) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K T) ∧
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (prG (NumberField.PlaceAbove.above E K v₀)) 2).hom
          (groupCohomology.π (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2 (groupCohomology.cocyclesMk ξ hξ)) =
        a • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀))) θ 2).hom u' ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (g : Fin 2 → (K ≃ₐ[E] K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v₀.asIdeal →
        finPart w (Additive.toMul (ξ g)) = 1) := by sorry
