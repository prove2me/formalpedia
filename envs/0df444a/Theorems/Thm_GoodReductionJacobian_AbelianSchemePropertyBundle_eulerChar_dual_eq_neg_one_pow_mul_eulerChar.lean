-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_dual_eq_neg_one_pow_mul_eulerChar
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_dual_eq_neg_one_pow_mul_eulerChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/2777c133-a5be-5c3d-9b1f-dc788f6dc41b
-- title:
--   Euler characteristic of the dual of an invertible sheaf
-- statement:
--   Let $K$ be an algebraically closed field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} K$ be a morphism. Assume given a relative group law $L$ for $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} K$, natural in $T$, and assume $L$ is commutative; assume also the project's bundle `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $g$ be a natural number with the instance asserting that $f$ is smooth of relative dimension $g$. Let $\mathcal{K}$ be an ordered affine cover of $A$: a finite, linearly ordered index type together with affine opens whose supremum is $\top$. Let $M$ be an $\mathcal{O}_A$-module which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback of $M$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules. Then the Euler characteristic, computed from the Čech data of $\mathcal{K}$ as the alternating sum $\sum_{i < \#\mathcal{K}.\iota} (-1)^i \dim_K H^i$, of the presheaf of sections of the dual $\mathcal{H}om(M, \mathbb{1})$ equals $(-1)^g$ times the same Euler characteristic of $M$.
--
--   This is the standard fact that on an abelian variety of dimension $g$ one has $\chi(M^{\vee}) = (-1)^g \chi(M)$ for invertible $M$, here formulated for the Čech Euler characteristic attached to a fixed finite ordered affine cover. It feeds into the computation relating $\chi(M)^2$ to a degree, used in the study of the Jacobian of $J_1$ with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_dual_eq_neg_one_pow_mul_eulerChar.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_dual_eq_neg_one_pow_mul_eulerChar
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    (OModulePresheaf.ofModules f (Scheme.Modules.dual M)).eulerChar 𝒦 =
      (-1) ^ g * (OModulePresheaf.ofModules f M).eulerChar 𝒦 := by sorry
