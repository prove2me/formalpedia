-- Prove2me | Theorems.Thm_NumberField_SIdele_exists_hom_ideles_apply_eq
-- name    : NumberField.SIdele.exists_hom_ideles_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/38221e9c-58ba-5190-afe7-1e7bd2f072e9
-- title:
--   Equivariance of Φ upgraded to a morphism of representations
-- statement:
--   Let $E$ and $K$ be number fields with $K$ a Galois extension of $E$, and let $G = \mathrm{Gal}(K/E)$ be realised as the group of $E$-algebra automorphisms of $K$. Let $S$ be a finite set of nonzero primes of $\mathcal{O}_E$, and write $J =$ [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) for the $\mathbb{Z}$-linear representation of $G$ obtained as the product, indexed by `Index E S`, of the fibre representations: at the finite indices the representations coinduced from the local units at the primes of $S$ and from the local integral units at the remaining primes, and at the archimedean indices the representations coinduced from the local units at the infinite places, each coinduction being along the inclusion of the corresponding decomposition subgroup. Let $D$ be an idèle Galois descent datum for $\mathcal{O}_K$, $E$, $K$, that is, a monoid homomorphism from $G$ to the ring automorphisms of the adèle ring `AdeleRing (𝓞 K) K` which is continuous in each $g$ and compatible with the structure map from $K$; let `D.unitsAct` be the induced action of $G$ on the unit group of the adèle ring by $\mathbb{Z}$-multiplicative automorphisms. Assume the unit group is equipped with a multiplicative distributive $G$-action whose scalar multiplication agrees pointwise with `D.unitsAct`. Let $\Phi$ be a homomorphism of additive groups from $J$ to the additive copy of the adèle unit group satisfying $\Phi(\rho(g)y) = g \cdot \Phi(y)$ for all $g \in G$ and $y \in J$, the action on the target being `D.unitsAct`. Then there is a morphism $\Phi_R$ in the category of $\mathbb{Z}$-linear representations of $G$ from $J$ to `Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ` whose underlying map sends every $y$ to $\Phi(y)$.
--
--   This is a packaging statement: an additive, $G$-equivariant map from the $S$-idèle module into the idèle unit group is recast as a morphism in the category of $\mathbb{Z}$-linear $G$-representations, the form required by machinery working with inhomogeneous cochains and functoriality of group cohomology. It is used in the level computations [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp) and [`NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d`](thm.html#NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_exists_hom_ideles_apply_eq.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

theorem NumberField.SIdele.exists_hom_ideles_apply_eq
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hΦρ : ∀ (g : K ≃ₐ[E] K) (y : NumberField.SIdele.obj E K S),
      Φ ((NumberField.SIdele.obj E K S).ρ g y) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ y)))) :
    ∃ ΦR : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ,
      ∀ y : NumberField.SIdele.obj E K S, ΦR.hom y = Φ y := by sorry
