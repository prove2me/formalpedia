-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b9722a5d-dd57-5b84-9c96-6a88884346a7
-- title:
--   Primitives of H inject into Čech H¹(𝒪_A)
-- statement:
--   Let $K$ be a field, $f : A \to \operatorname{Spec} K$ a morphism of schemes, and $L$ a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $K$, assumed commutative; assume the bundle `AbelianSchemePropertyBundle` for $f$ ($f$ smooth and proper, with connected fibres, and admitting some relative group law). Let $n$ be a natural number such that the morphism $[n] =$ `L.schemeNsmul n` obtained by applying $L$'s $n$-fold multiplication to the identity point is finite, flat and surjective. Let $H$ be a finite commutative cocommutative Hopf $K$-algebra, equipped with a family of bijections $e_T$, for all commutative $K$-algebras $T$, from the convolution monoid of $K$-algebra maps $H \to T$ onto the set of $n$-torsion $T$-points of $L$, carrying the convolution product to the group law (`he_mul`) and natural in $T$ along $K$-algebra maps (`he_nat`). Let $\mathrm{act}$ be a morphism $A \times_K \operatorname{Spec} H \to A$ over $K$ which on points sends $(x,\varphi)$ to $L$-sum $x + e_T(\varphi)$ (`hpts`), satisfying $\mathrm{pr}_1 \circ [n] = \mathrm{act} \circ [n]$ in diagrammatic order, and such that the resulting shear morphism $A \times_K \operatorname{Spec} H \to A \times_{[n],A,[n]} A$ is an isomorphism. Then for every finite linearly ordered cover $\mathcal{K}$ of $A$ by affine opens there exists an injective $K$-linear map from the primitives of $H$, the submodule of $h$ with $\Delta h = h \otimes 1 + 1 \otimes h$, into `(OModulePresheaf.unit f).HSucc 𝒦 0`, the first cohomology $\ker d^1 / \operatorname{im} d^0$ of the Čech complex of $\mathcal{K}$ with values in the presheaf $U \mapsto \Gamma(A,U)$.
--
--   This is the cohomological half of the classical statement that when $[n] : A \to A$ is an $A[n]$-torsor, homomorphisms $A[n] \to \mathbb{G}_a$ — equivalently the primitive elements of the Hopf algebra $H$ of $A[n]$ — give rise to classes in $H^1(A, \mathcal{O}_A)$; the torsor structure itself enters as the hypothesis block on $\mathrm{act}$ and the shear morphism. It is used by the variant whose hypotheses are stated purely in terms of the torsion-point dictionary $e$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (hsurj : Function.Surjective (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (act : pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ⟶ A)
    (hact : act ≫ f = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f)
    (hpts : ∀ (T : Type u) [CommRing T] [Algebra K T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f) (φ : WithConv (H →ₐ[K] T))
        (hx : x.1 ≫ f = Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K H))),
      pullback.lift x.1 (Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T))) hx ≫ act =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K T))) x (e T φ).val).1)
    (hsh : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n)
    (hiso : IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh))
    (𝒦 : A.OrderedAffineCover) :
    ∃ θ : ↥(primitives K H) →ₗ[K] (OModulePresheaf.unit f).HSucc 𝒦 0, Function.Injective θ := by sorry
