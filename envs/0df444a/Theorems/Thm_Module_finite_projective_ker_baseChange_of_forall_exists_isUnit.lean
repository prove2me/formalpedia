-- Prove2me | Theorems.Thm_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit
-- name    : Module.finite_projective_ker_baseChange_of_forall_exists_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b97c7231-c0d4-54f0-b57b-b22f0d3567ff
-- title:
--   Zariski-local criterion for ker(δ⊗ A) finite projective of rank r
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative $R$-algebra, and let $C^0$, $C^1$, $F$ be $R$-modules, all in one universe; let $\delta : C^0 \to C^1$ and $\Theta : F \to C^0$ be $R$-linear maps and $r$ a natural number. Assume the following local hypothesis: for every point $\mathfrak q$ of $\operatorname{Spec} A$ there is an element $g \in R$ whose image in $A$ does not lie in the prime ideal $\mathfrak q$, such that for every commutative $R$-algebra $A'$ in which the image of $g$ is a unit, the kernel of the base-changed map $\delta \otimes_R A' : C^0 \otimes_R A' \to C^1 \otimes_R A'$ is a finite $A'$-module, is projective over $A'$, has rank at the stalk equal to $r$ at every point of $\operatorname{Spec} A'$, and is contained in the image of $\Theta \otimes_R A'$. The conclusion is that these same four assertions hold for $A$ itself: $\ker(\delta \otimes_R A)$ is a finite projective $A$-module whose rank at every stalk of $\operatorname{Spec} A$ equals $r$, and it is contained in the image of $\Theta \otimes_R A$.
--
--   This is a Zariski local-to-global statement: the four properties of the degree-zero cohomology of the base-changed two-term complex (finiteness, projectivity, constant stalkwise rank $r$, and being covered by $\Theta$) are local on the base and hence descend from a cover of $\operatorname{Spec} A$ by basic opens coming from elements of $R$. It is used in the construction of points of the Hilbert functor, in [`AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.finite_projective_ker_baseChange_of_forall_exists_isUnit
    {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    {C0 C1 F : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup F] [Module R F]
    (δ : C0 →ₗ[R] C1) (Θ : F →ₗ[R] C0) (r : ℕ)
    (hloc : ∀ 𝔮 : PrimeSpectrum A, ∃ g : R, algebraMap R A g ∉ 𝔮.asIdeal ∧
      ∀ (A' : Type u) [CommRing A'] [Algebra R A'], IsUnit (algebraMap R A' g) →
        Module.Finite A' (LinearMap.ker (δ.baseChange A')) ∧
        Module.Projective A' (LinearMap.ker (δ.baseChange A')) ∧
        (∀ 𝔮' : PrimeSpectrum A', Module.rankAtStalk (LinearMap.ker (δ.baseChange A')) 𝔮' = r) ∧
        LinearMap.ker (δ.baseChange A') ≤ LinearMap.range (Θ.baseChange A')) :
    Module.Finite A (LinearMap.ker (δ.baseChange A)) ∧
    Module.Projective A (LinearMap.ker (δ.baseChange A)) ∧
    (∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (LinearMap.ker (δ.baseChange A)) 𝔮 = r) ∧
    LinearMap.ker (δ.baseChange A) ≤ LinearMap.range (Θ.baseChange A) := by sorry
