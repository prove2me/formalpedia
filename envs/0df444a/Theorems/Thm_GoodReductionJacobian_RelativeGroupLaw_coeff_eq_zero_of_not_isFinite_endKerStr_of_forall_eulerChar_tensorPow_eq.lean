-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/ce9977b0-2036-5b5e-b629-7c5052227be5
-- title:
--   Vanishing degree-g coefficient of χ((γ^*L)^{⊗ m}) for non-isogenies
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism, equipped with a `RelativeGroupLaw` $L$: functorial multiplication, unit and inversion maps on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over each $K$-scheme $(T,t)$, satisfying associativity, the unit laws, left inversion and compatibility with base change. Assume $f$ carries an `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre of $f$ over a point of $\operatorname{Spec} K$ is connected, and $f$ admits a relative group law. Let $g$ be a natural number with $f$ smooth of relative dimension $g$, let $\mathcal K$ be a cover of $A$ by finitely many affine opens indexed by a linearly ordered type, let $\mathcal L$ be an $\mathcal O_A$-module which is invertible (locally isomorphic to the unit module on a neighbourhood of each point), and let $\gamma : A \to A$ satisfy $\gamma \circ f = f$ together with the hypothesis that for every $K$-scheme $(T,t)$ and all $x,y \in A(T)$ one has $\gamma \circ (x \cdot y) = (\gamma \circ x)\cdot(\gamma \circ y)$ for the group law $L$. Assume the structure morphism to $\operatorname{Spec} K$ of the kernel $\ker \gamma$, namely the second projection of the pullback of $\gamma$ along the unit section over $\operatorname{id}_{\operatorname{Spec} K}$, is not finite. Finally let $p \in \mathbb Q[X]$ be such that for every $m \in \mathbb N$ the Euler characteristic of the $\mathcal O$-module presheaf of sections of $(\gamma^*\mathcal L)^{\otimes m}$ — the alternating sum $\sum_i (-1)^i \dim_K \check H^i$ of the Čech ranks over the cover $\mathcal K$, with the tensor power formed as the iterated tensor product starting from the unit module — equals $p(m)$. Then the coefficient of $X^g$ in $p$ is zero.
--
--   This is the degenerate case of the projection formula for intersection numbers: up to the factor $g!$ the degree-$g$ coefficient of the Snapper polynomial is the top self-intersection number $((\gamma^*\mathcal L)^g)$, which vanishes precisely because $\gamma$ fails to be an isogeny. It is used to establish the identity $((\gamma^*\mathcal L)^g) = \deg\gamma \cdot (\mathcal L^g)$, with the convention $\deg \gamma = 0$ for non-isogenies, in [`GoodReductionJacobian.RelativeGroupLaw.coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq`](thm.html#GoodReductionJacobian.RelativeGroupLaw.coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (γ : SchemeHomOver f f)
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    (hker : ¬ IsFinite (L.endKerStr γ))
    (p : Polynomial ℚ)
    (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
        (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ)) :
    p.coeff g = 0 := by sorry
