-- Prove2me | Theorems.Thm_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
-- name    : NeronModelInfra.exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/a0492927-9b78-5878-89cc-3ed7c98cf75b
-- title:
--   Points of a local scheme factor through an affine chart
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $f : X \to \operatorname{Spec} R$ a morphism, and let $R'$ be a commutative local ring equipped with an $R$-algebra structure. Let $x$ be a morphism over $\operatorname{Spec} R$ from $\operatorname{Spec} R'$ to $X$, that is (unfolding `SchemeHomOver`) a pair consisting of a scheme morphism $x_1 : \operatorname{Spec} R' \to X$ together with a proof that $x_1$ followed by $f$ equals $\operatorname{Spec}$ applied to the structure map $R \to R'$. Let $U$ be an open subscheme of $X$ which is affine (`IsAffineOpen`), and assume that the image of the closed point of $R'$ under $x_1$ lies in $U$. Endow $\Gamma(X, U)$ with the $R$-algebra structure obtained by composing the inverse of the isomorphism $R \cong \Gamma(\operatorname{Spec} R, \top)$, the map $f^{\sharp}$ on global sections $\Gamma(\operatorname{Spec} R, \top) \to \Gamma(X, \top)$, and the restriction $\Gamma(X, \top) \to \Gamma(X, U)$. Then there exists an $R$-algebra homomorphism $c : \Gamma(X, U) \to R'$ such that the preimage under $c$ of the maximal ideal of $R'$ is exactly the prime ideal of $\Gamma(X, U)$ attached by `IsAffineOpen.primeIdealOf` to the point $x_1(\mathfrak m_{R'})$ of $U$.
--
--   This is the standard dictionary between a $\operatorname{Spec}$-of-a-local-ring point of an $R$-scheme whose closed point lands in an affine chart and an $R$-algebra map out of the coordinate ring of that chart, together with the identification of the contracted maximal ideal as the prime of the specialisation. It serves as the chart-level bookkeeping for index-one points in the Néron smoothening material, and is used in the construction of the strata where smoothness and freeness of the relevant loci are tested.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem.lean

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem NeronModelInfra.exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f)
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : x.1 (IsLocalRing.closedPoint R') ∈ U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    ∃ c : Γ(X, U) →ₐ[R] R',
      (IsLocalRing.maximalIdeal R').comap c = (hU.primeIdealOf ⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩).asIdeal := by sorry
