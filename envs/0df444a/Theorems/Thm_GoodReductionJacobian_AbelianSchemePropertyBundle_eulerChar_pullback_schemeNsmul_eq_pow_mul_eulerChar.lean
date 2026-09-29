-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_pullback_schemeNsmul_eq_pow_mul_eulerChar
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_pullback_schemeNsmul_eq_pow_mul_eulerChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a55859f4-7829-5d50-b86e-6ff4ffe087e9
-- title:
--   Pull-back along [n] multiplies χ of a line bundle by n^{2g}
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme, and $f : A \to \operatorname{Spec} K$ a morphism, equipped with a relative group law $L$ in the sense of the project, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} K$, natural in $T$; assume $L$ is commutative, i.e. the multiplication on each such set of $T$-points is commutative. Assume further the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $g$ be a natural number with $f$ smooth of relative dimension $g$, and let $n$ be a natural number whose image in $K$ is nonzero. Let $\mathcal F$ be an $\mathcal O_A$-module that is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal F$ is isomorphic to the unit module, and let $\mathcal F'$ be an $\mathcal O_A$-module together with an isomorphism $\mathcal F' \cong [n]^*\mathcal F$, the pull-back of $\mathcal F$ along the morphism $A \to A$ obtained from the $n$-fold sum of the identity point in the group law $L$. Finally let $\mathcal K$ and $\mathcal K'$ be ordered affine covers of $A$, each consisting of a finite linearly ordered family of affine opens covering $A$. Then the Euler characteristic of the $\mathcal O$-module presheaf of sections of $\mathcal F'$, computed as the alternating sum $\sum_i (-1)^i \dim_K$ of the Čech groups for the cover $\mathcal K'$, equals $n^{2g}$ times the corresponding alternating sum for $\mathcal F$ and the cover $\mathcal K$. In particular the two covers may be chosen independently of each other.
--
--   This is the case of multiplication by $n$ of the classical formula $\chi(\varphi^*\mathcal F) = \deg(\varphi)\,\chi(\mathcal F)$ for an isogeny $\varphi$ of abelian varieties, with $\deg [n] = n^{2g}$ when $n$ is invertible on the base. It is used to obtain the Riemann–Roch monomial $\chi(\mathcal M^{\otimes m}) = m^g \chi(\mathcal M)$ and the vanishing of the Euler characteristic of the structure sheaf, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_eulerChar_tensorPow_eq_mul_pow`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_eulerChar_tensorPow_eq_mul_pow) and [`GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinite_unit_and_eulerChar_unit_eq_zero`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinite_unit_and_eulerChar_unit_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_pullback_schemeNsmul_eq_pow_mul_eulerChar.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_pullback_schemeNsmul_eq_pow_mul_eulerChar
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (𝓕 : A.Modules) (h𝓕 : Scheme.Modules.IsInvertible 𝓕)
    (𝓕' : A.Modules) (e : 𝓕' ≅ (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓕)
    (𝒦 𝒦' : A.OrderedAffineCover) :
    (OModulePresheaf.ofModules f 𝓕').eulerChar 𝒦' = (n : ℤ) ^ (2 * g) * (OModulePresheaf.ofModules f 𝓕).eulerChar 𝒦 := by sorry
