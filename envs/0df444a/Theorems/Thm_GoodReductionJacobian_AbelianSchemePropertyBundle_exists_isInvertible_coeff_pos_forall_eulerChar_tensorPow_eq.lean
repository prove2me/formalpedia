-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_coeff_pos_forall_eulerChar_tensorPow_eq
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_coeff_pos_forall_eulerChar_tensorPow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/ed5a600a-7ca8-567a-87b4-63a885d8013f
-- title:
--   Invertible sheaf on A with positive m^g-coefficient of χ
-- statement:
--   Let $K$ be an algebraically closed field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} K$ be a morphism satisfying the bundle of properties `AbelianSchemePropertyBundle`, namely: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} K$ the fibre $f^{-1}(\{s\})$ is a connected topological space, and the functor of points of $f$ carries a relative group law (a `RelativeGroupLaw`: multiplication, unit and inverse operations on $T$-points over $\operatorname{Spec} K$, associative, unital, with left inverses, and natural in $T$). Let $g$ be a natural number such that $f$ is smooth of relative dimension $g$, and let $\mathcal K$ be an ordered affine cover of $A$, that is, a finite linearly ordered index type together with affine open subschemes $U_i \subseteq A$ whose supremum is $\top$. Then there exist a sheaf of modules $\mathcal L$ on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with the pullback of $\mathcal L$ along $U \hookrightarrow A$ isomorphic to the unit sheaf of modules on $U$, and a polynomial $q \in \mathbb Q[X]$ with $q$'s coefficient of $X^g$ strictly positive, such that for every natural number $m$ the Euler characteristic $\sum_i (-1)^i \dim_K$ of the alternating Čech modules of the presheaf of sections of $\mathcal L^{\otimes m}$ on $\mathcal K$, where $\mathcal L^{\otimes 0}$ is the unit and $\mathcal L^{\otimes (n+1)} = \mathcal L^{\otimes n} \otimes \mathcal L$, equals $q(m)$ as a rational number, the integer-valued Euler characteristic being cast into $\mathbb Q$.
--
--   This is the combination, in the form needed here, of the projectivity of abelian varieties with Snapper's theorem: a suitable invertible sheaf on an abelian variety of dimension $g$ has $\chi(\mathcal L^{\otimes m})$ a polynomial in $m$ of degree exactly $g$ with positive leading coefficient. It feeds the computation of the degree of an endomorphism of an abelian scheme carrying a relative group law, via [`GoodReductionJacobian.RelativeGroupLaw.exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_coeff_pos_forall_eulerChar_tensorPow_eq.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_coeff_pos_forall_eulerChar_tensorPow_eq
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ ∃ q : Polynomial ℚ, 0 < q.coeff g ∧
      ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ) := by sorry
