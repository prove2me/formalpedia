-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_of_surjective
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/dd9fbb0f-86d0-5344-b691-5a8332df7bfe
-- title:
--   Surjective endomorphisms have finite kernel scheme
-- statement:
--   Let $K$ be an algebraically closed field, let $A$ be a scheme, and let $f : A \to \operatorname{Spec} K$ be a morphism. Let $L$ be a relative group law on $f$, that is, a group structure on the set of sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for every $K$-scheme $(T,t)$ — operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ satisfying associativity, both unit laws and left inverse, and natural in $(T,t)$ under precomposition with any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume $hA$: $f$ is smooth, $f$ is proper, the fibre $f^{-1}(s)$ is connected for every point $s$ of $\operatorname{Spec} K$, and $f$ admits some relative group law. Let $\gamma : A \to A$ satisfy $\gamma$ followed by $f$ equal to $f$, and assume $\gamma$ is a homomorphism for $L$: for every $K$-scheme $(T,t)$ and all sections $x,y$, postcomposing $\mathrm{mul}\,t\,x\,y$ with $\gamma$ equals $\mathrm{mul}\,t$ applied to $x$ followed by $\gamma$ and $y$ followed by $\gamma$. Assume further that $\gamma$ is surjective. Then the projection $\operatorname{pullback}(\gamma, e) \to \operatorname{Spec} K$, where $e : \operatorname{Spec} K \to A$ is the unit section $\mathrm{one}$ at the identity of $\operatorname{Spec} K$, is a finite morphism.
--
--   This is the classical assertion that a surjective endomorphism of an abelian variety over an algebraically closed field is an isogeny, in the form: the kernel group scheme $\gamma^{-1}(0)$ is finite over the base. It is used in the treatment of endomorphism degrees for relative group laws, in particular in showing that the degree of an endomorphism coming from a nontrivial quaternionic action on a fake elliptic curve is nonzero, and in a vanishing criterion for coefficients attached to Euler characteristics of tensor powers. The proof invokes the integrality of $A$ supplied by [`GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_of_field`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_of_field).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_of_surjective.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_of_surjective
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (γ : SchemeHomOver f f)
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    [Surjective γ.1] :
    IsFinite (L.endKerStr γ) := by sorry
