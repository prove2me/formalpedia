-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_eq_mul_of_ne_zero
-- name    : GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_eq_mul_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/9a60403a-94d8-51d0-890f-06513220846e
-- title:
--   Multiplicativity of `endDegree` under composition of isogenies
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $K$-morphisms over arbitrary $t : T \to \operatorname{Spec} K$ (multiplication, unit and inverse, associativity, unit and inverse laws, and compatibility with base change along $\psi : T' \to T$). Assume $L$ is commutative, that $f$ satisfies the bundle `AbelianSchemePropertyBundle`, i.e. $f$ is smooth, proper, has connected fibres and admits some relative group law, and that $f$ is smooth of relative dimension $g$ for some $g \in \mathbb{N}$. Let $\beta, \gamma$ be endomorphisms of $A$ over $\operatorname{Spec} K$, that is, morphisms $A \to A$ commuting with $f$, each assumed to respect the group law in the functorial sense: post-composition with $\beta$ (resp. $\gamma$) carries $L$-products of sections to $L$-products of their post-compositions. Here $L.\mathrm{endDegree}\,\beta$ is the finrank at the closed point of $\operatorname{Spec} K$ of the structure morphism of the pullback of $\beta$ along the unit section, when that structure morphism is finite, and $0$ otherwise. If $L.\mathrm{endDegree}\,\beta \ne 0$ and $L.\mathrm{endDegree}\,\gamma \ne 0$, then the composite $\beta$ followed by $\gamma$ satisfies $L.\mathrm{endDegree}(\gamma \circ \beta) = L.\mathrm{endDegree}\,\beta \cdot L.\mathrm{endDegree}\,\gamma$.
--
--   This is the multiplicativity of the degree of isogenies of an abelian variety over an algebraically closed field, in the form used for endomorphisms of the Jacobian setting. It is invoked in the computation of degrees of endomorphisms coming from quaternionic multiplication on fake elliptic curves, and in identifying the inverse endomorphism as one of degree one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_eq_mul_of_ne_zero.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_eq_mul_of_ne_zero
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (β γ : SchemeHomOver f f)
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) β =
        L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β))
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    (hβ0 : L.endDegree β ≠ 0) (hγ0 : L.endDegree γ ≠ 0) :
    L.endDegree (NeronModelInfra.schemeHomOverComp β γ) = L.endDegree β * L.endDegree γ := by sorry
