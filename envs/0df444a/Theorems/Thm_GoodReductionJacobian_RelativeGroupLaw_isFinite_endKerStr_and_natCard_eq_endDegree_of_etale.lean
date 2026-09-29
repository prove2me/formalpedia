-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/b335a782-54c7-51c1-979f-90d5d41b9382
-- title:
--   Étale kernel of an endomorphism: finiteness and degree
-- statement:
--   Let $K$ be an algebraically closed field, let $A$ be a scheme and let $f\colon A \to \operatorname{Spec} K$ be a proper morphism. Let $L$ be a relative group law on $f$: for every $K$-scheme $t\colon T \to \operatorname{Spec} K$ a multiplication, unit and inversion on the set $\{\varphi\colon T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, the unit laws and left inversion, and compatible with pullback along morphisms $\psi\colon T' \to T$ over $\operatorname{Spec} K$. Let $\beta$ be a morphism $A \to A$ with $\beta$ followed by $f$ equal to $f$, and write $0 = L.\mathrm{one}(\mathrm{id}_{\operatorname{Spec} K})\colon \operatorname{Spec} K \to A$ for the unit section. Form $\ker\beta = A \times_{\beta, A, 0} \operatorname{Spec} K$ with its second projection to $\operatorname{Spec} K$, and assume this projection is étale. Then: (i) the projection $\ker\beta \to \operatorname{Spec} K$ is finite; (ii) the set of $x\colon \operatorname{Spec} K \to A$ with $x$ followed by $f$ equal to $\mathrm{id}$ and $x$ followed by $\beta$ equal to $0$ is finite; and (iii) its cardinality equals $L.\mathrm{endDegree}\,\beta$, namely the rank of $\ker\beta \to \operatorname{Spec} K$ at the closed point of $\operatorname{Spec} K$ (this being the value of $\mathrm{endDegree}$ once finiteness holds).
--
--   This is the standard count for a separable isogeny of a proper group scheme over an algebraically closed field: the kernel is a finite étale scheme, hence a disjoint union of copies of $\operatorname{Spec} K$, so its $K$-points number exactly its degree. It is used wherever degrees of endomorphisms are computed by counting rational points, for instance in the study of the Picard group of a curve in characteristic $p$ and in the construction of level structures on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    [IsProper f]
    (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) [Etale (L.endKerStr β)] :
    IsFinite (L.endKerStr β) ∧
      Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        NeronModelInfra.schemeHomOverComp x β = L.one (𝟙 (Spec (CommRingCat.of K)))} ∧
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        NeronModelInfra.schemeHomOverComp x β = L.one (𝟙 (Spec (CommRingCat.of K)))} = L.endDegree β := by sorry
