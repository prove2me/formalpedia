-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_torsion_points_equiv
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_torsion_points_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/10b96fb8-a9f9-5848-abcf-da060a447d13
-- title:
--   Translation torsor: [n] : A → A under Spec H
-- statement:
--   Let $K$ be a field and $f : A \to \operatorname{Spec} K$ a scheme over $K$, equipped with a relative group law $L$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over each $t : T \to \operatorname{Spec} K$, compatible with base change along $T' \to T$; assume $L$ is commutative, i.e. `L.mul t x y = L.mul t y x` for all $t$ and all points $x,y$. Let $n : \mathbb{N}$ and let `L.schemeNsmul n` be the morphism $A \to A$ obtained as the $n$-fold $L$-sum of the identity point of $A$ over $f$; assume it is finite and flat. Let $H$ be a commutative Hopf algebra over $K$, finite-dimensional as a $K$-module and cocommutative, and suppose given, for each commutative $K$-algebra $T$, a bijection $e_T$ from the convolution monoid `WithConv (H →ₐ[K] T)` onto the set of points $x$ of $A$ over $\operatorname{Spec} T \to \operatorname{Spec} K$ with $L$-$n$-fold sum of $x$ equal to the identity point, such that $e_T$ carries the convolution product to `L.mul` (`he_mul`) and is natural in $T$: for a $K$-algebra map $g' : T \to T'$ and $\varphi$, the underlying morphism of $e_{T'}(g' \circ \varphi)$ is $\operatorname{Spec} g'$ followed by that of $e_T(\varphi)$ (`he_nat`). Then there is a morphism $act$ from the fibre product of $f$ and $\operatorname{Spec}$ of the structure map $K \to H$ to $A$ such that: $act$ followed by $f$ equals the first projection followed by $f$; for every commutative $K$-algebra $T$, every point $x$ of $A$ over $\operatorname{Spec} T$, every $\varphi$ in `WithConv (H →ₐ[K] T)` and every proof that $x$ followed by $f$ equals $\operatorname{Spec} \varphi$ followed by $\operatorname{Spec}(K \to H)$, the induced map $\operatorname{Spec} T \to$ the fibre product composed with $act$ equals the underlying morphism of `L.mul` of $x$ and $e_T(\varphi)$; and, for the resulting identity $\mathrm{pr}_1$ followed by `L.schemeNsmul n` $=$ $act$ followed by `L.schemeNsmul n`, the induced morphism from the fibre product of $f$ and $\operatorname{Spec}(K \to H)$ to the fibre product of `L.schemeNsmul n` with itself, with components $\mathrm{pr}_1$ and $act$, is an isomorphism.
--
--   This is the statement that translation by the $n$-torsion makes $[n] : A \to A$ a torsor under the finite group scheme $\operatorname{Spec} H$ representing $A[n]$: the action morphism exists, is given on points by $x \mapsto x + e_T(\varphi)$, commutes with $[n]$, and the associated shear map $(x,t) \mapsto (x, x+t)$ is an isomorphism onto $A \times_{[n],A,[n]} A$. It feeds the analysis of invariant differentials and primitive elements on the Hopf algebra $H$ used later in the good-reduction study of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_torsion_points_equiv.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_torsion_points_equiv
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1) :
    ∃ (act : pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ⟶ A),

      act ≫ f = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f ∧

      (∀ (T : Type u) [CommRing T] [Algebra K T]
          (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f) (φ : WithConv (H →ₐ[K] T))
          (hx : x.1 ≫ f = Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap K H))),
        pullback.lift x.1 (Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T))) hx ≫ act =
          (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K T))) x (e T φ).val).1) ∧

      ∃ (hsh : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ L.schemeNsmul n =
          act ≫ L.schemeNsmul n),
        IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n)
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh) := by sorry
