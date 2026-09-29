-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat
-- name    : GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_of_isFinite_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/315068b2-20a9-55e7-9a1e-83210578bd81
-- title:
--   Multiplicativity of degree for finite flat endomorphisms
-- statement:
--   Let $K$ be a field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} K$ be a morphism that is locally of finite type, with the underlying topological space of $A$ preconnected. Let $L$ be a relative group law on $f$ in the sense of the project's structure `RelativeGroupLaw`: a group structure (multiplication, unit, inverse, with associativity, unit laws, left inverse law) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points of each $K$-scheme $t : T \to \operatorname{Spec} K$, whose multiplication is natural under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} K$. Let $\beta, \gamma$ be endomorphisms of $A$ over $K$, i.e. morphisms $A \to A$ whose composition with $f$ is $f$, and assume each of the underlying morphisms is finite and flat. For such an endomorphism $\delta$, $L.\mathrm{endDegree}\,\delta$ is defined to be the rank, at the closed point of $\operatorname{Spec} K$, of the second projection from the fibre product of $\delta$ with the unit section $L.\mathrm{one}(\mathbf 1_{\operatorname{Spec} K})$ down to $\operatorname{Spec} K$, provided that projection is finite, and $0$ otherwise. The conclusion is that the endomorphism obtained by composing, $\beta$ followed by $\gamma$, satisfies $L.\mathrm{endDegree}(\gamma \circ \beta) = L.\mathrm{endDegree}(\beta)\cdot L.\mathrm{endDegree}(\gamma)$.
--
--   This is multiplicativity of the degree for isogenies, in the form: the order of the kernel of a composite of two finite flat endomorphisms of a connected group scheme over a field is the product of the two orders. It is used in the study of degrees of endomorphisms of Jacobians and of fake elliptic curves, for instance in the results on $\mathrm{Pic}^0$ and resultants attached to the Frobenius pushforward and in the numerical estimates for endomorphisms of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_of_isFinite_of_flat
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [PreconnectedSpace A] (L : RelativeGroupLaw K f) (β γ : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [IsFinite γ.1] [Flat γ.1] :
    L.endDegree (NeronModelInfra.schemeHomOverComp β γ) = L.endDegree β * L.endDegree γ := by sorry
