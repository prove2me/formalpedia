-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_nsmulPt_eq_one_of_forall_comp_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_nsmulPt_eq_one_of_forall_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/977be1e1-61c2-536c-81c2-260411d374ff
-- title:
--   Torsion points are determined by their geometric points
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$: a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $A$ over each $t : T \to \operatorname{Spec} R$, with multiplication, unit and inversion satisfying associativity, the unit laws, left inversion, and compatibility with base change along $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Fix $n \in \mathbb{N}$ and assume the structure morphism $L.\mathrm{schemeKerStr}\,n$, the second projection of the pullback of $L.\mathrm{schemeNsmul}\,n : A \to A$ against the unit section $(L.\mathrm{one}\,(\mathbb{1}))_1$ over $\operatorname{Spec} R$, is finite and étale. Let $t : T \to \operatorname{Spec} R$ and let $P, Q$ be $T$-points of $A$ over $t$ such that the $n$-fold iterate $\mathrm{nsmulPt}\,L\,t\,n$ (defined by $0 \mapsto L.\mathrm{one}\,t$ and $m+1 \mapsto L.\mathrm{mul}\,t\,(\mathrm{nsmulPt}\,L\,t\,m\,\cdot)\,\cdot$) sends each of $P$ and $Q$ to $L.\mathrm{one}\,t$. If for every algebraically closed field $k$ and every $\tau : \operatorname{Spec} k \to T$ the composites $\tau$ followed by $P$ and $\tau$ followed by $Q$ agree, then $P = Q$.
--
--   This is the rigidity statement for finite étale torsion subgroup schemes: two $n$-torsion sections over a base $T$, not assumed reduced, coincide as soon as they coincide on all geometric points. It is used in the construction and comparison of extra level structures on fake elliptic curves, being cited in the treatment of full level structures, of transport of rigidifications, and of Atkin–Lehner quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_nsmulPt_eq_one_of_forall_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_nsmulPt_eq_one_of_forall_comp_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) [IsFinite (L.schemeKerStr n)] [Etale (L.schemeKerStr n)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) (hQ : nsmulPt L t n Q = L.one t)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (τ : Spec (CommRingCat.of k) ⟶ T), τ ≫ P.1 = τ ≫ Q.1) :
    P = Q := by sorry
