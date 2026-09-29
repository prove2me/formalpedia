-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_mul_eulerChar_dual_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_mul_eulerChar_dual_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/9afb5659-f0d7-5519-941a-3003a0e3c5a0
-- title:
--   Riemann–Roch: χ(M)χ(M^∨)=(-1)^grkK(M)
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism, equipped with a relative group law $L$ on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} K$, natural in $T$; assume $L$ is commutative, and that `AbelianSchemePropertyBundle K f` holds, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} K$ is connected, and $f$ admits a relative group law. Let $g$ be a natural number with $f$ smooth of relative dimension $g$, let $\mathcal K$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens with supremum $\top$), and let $M$ be a module on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with the restriction of $M$ to $U$ isomorphic to the unit module. Let $\kappa : KM \to A$ be a closed immersion such that $\kappa$ followed by $f$ is finite, and assume that for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $x : \operatorname{Spec} R \to A$ over $t$, the point $x$ factors through $\kappa$ if and only if `L.IsInStabilizer M t x` holds, i.e. the pullback of $M$ along right translation by $x$ is locally isomorphic, over the second projection of $A \times_{\operatorname{Spec} K} \operatorname{Spec} R$, to the pullback of $M$ along the first projection. Then the Euler characteristic of $M$ computed from the Čech complex of the $\mathcal O$-module presheaf of $M$ with respect to $\mathcal K$ — the alternating sum $\sum_i (-1)^i \dim_K H^i$ over indices below the cardinality of the index type of $\mathcal K$ — multiplied by the corresponding Euler characteristic of the dual module $\underline{\operatorname{Hom}}(M, \mathbf 1)$, equals $(-1)^g$ times the rank of the finite morphism $\kappa$ followed by $f$ at the closed point of $\operatorname{Spec} K$, viewed as an integer.
--
--   This is Mumford's form of the Riemann–Roch theorem on an abelian variety: the product of the Euler characteristics of an invertible sheaf and its dual is $(-1)^g$ times the length of the stabiliser subscheme $K(\mathcal M)$, the latter being presented here by a finite closed subscheme representing the stabiliser on affine test points. It feeds the statement that $\chi(\mathcal M)^2$ equals that rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_mul_eulerChar_dual_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_mul_eulerChar_dual_eq_neg_one_pow_mul_finrank_of_forall_iff_isInStabilizer
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x) :
    (OModulePresheaf.ofModules f M).eulerChar 𝒦 * (OModulePresheaf.ofModules f (Scheme.Modules.dual M)).eulerChar 𝒦 =
      (-1) ^ g * ((κ ≫ f).finrank (IsLocalRing.closedPoint K) : ℤ) := by sorry
