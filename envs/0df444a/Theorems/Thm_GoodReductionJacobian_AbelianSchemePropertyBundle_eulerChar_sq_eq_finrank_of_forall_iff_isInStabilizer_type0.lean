-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_sq_eq_finrank_of_forall_iff_isInStabilizer_type0
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_sq_eq_finrank_of_forall_iff_isInStabilizer_type0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/cd3cc5a3-99d4-53a5-ba97-5938e597152d
-- title:
--   Mumford's Riemann–Roch: χ(M)²=rankK(M)
-- statement:
--   Let $K$ be an algebraically closed field, let $f : A \to \operatorname{Spec} K$ be a morphism of schemes, and let $L$ be a relative group law for $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = t\}$ of $T$-points over $K$, compatible with base change along morphisms $T' \to T$; assume $L$ is commutative, and assume the property bundle `AbelianSchemePropertyBundle K f`, which asserts that $f$ is smooth and proper, that every fibre of $f$ is connected, and that a relative group law for $f$ exists. Let $g$ be a natural number with $f$ smooth of relative dimension $g$, let $\mathcal{K}$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens with supremum $\top$), and let $M$ be a module on $A$ that is invertible, i.e. locally isomorphic to the unit module. Let $\kappa : K_M \to A$ be a closed immersion such that $\kappa$ followed by $f$ is finite, and assume that for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $R$-point $x$ of $A$ over $t$, the point $x$ factors through $\kappa$ if and only if `L.IsInStabilizer M t x` holds, i.e. the pullback of $M$ along right translation by $x$ and the pullback of $M$ along the first projection of $A \times_K \operatorname{Spec} R$ are locally isomorphic over the second projection. Then the square of the Euler characteristic of the $\mathcal{O}$-module presheaf of sections of $M$, taken with respect to $\mathcal{K}$ (the alternating sum of the $K$-dimensions of the associated Čech modules over the index range of $\mathcal{K}$), equals the integer $(\kappa \circ f)$-$\mathrm{finrank}$ at the closed point of $K$.
--
--   This is the kernel-order form of Mumford's Riemann–Roch theorem for an invertible module on an abelian variety over an algebraically closed field: $\chi(M)^2$ equals the degree of the polarisation morphism $\varphi_M$, presented here as the rank over $K$ of the finite stabiliser scheme $K(M)$, which enters via a hypothesis characterising its points rather than via a representability statement. It is used downstream in the treatment of polarised abelian schemes, Riemann forms and quaternionic multiplication, where divisibility and non-vanishing properties of Euler characteristics are extracted from kernel orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_sq_eq_finrank_of_forall_iff_isInStabilizer_type0.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_sq_eq_finrank_of_forall_iff_isInStabilizer_type0
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x) :
    ((OModulePresheaf.ofModules f M).eulerChar 𝒦) ^ 2 = ((κ ≫ f).finrank (IsLocalRing.closedPoint K) : ℤ) := by sorry
