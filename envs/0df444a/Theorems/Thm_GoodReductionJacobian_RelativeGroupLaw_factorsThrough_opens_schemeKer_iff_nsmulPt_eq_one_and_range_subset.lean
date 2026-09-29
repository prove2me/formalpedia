-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset
-- name    : GoodReductionJacobian.RelativeGroupLaw.factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/1da0dd73-5c78-5d0b-bf30-f169c23e3b6c
-- title:
--   Points factoring through an open part of A[n]
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$: a functorial group law on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $A$ over $\operatorname{Spec} R$, given by multiplication, unit and inverse operations satisfying associativity, the unit laws, left inverses, and naturality of multiplication under base change $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Fix $n \in \mathbb{N}$; write $[n] =$ `L.schemeNsmul n` for the endomorphism of $A$ obtained as the underlying morphism of the $n$-th multiple of the identity point, $e = (L.one (\mathbb{1}_{\operatorname{Spec} R})).1$ for the unit section, and $A[n] =$ `L.schemeKer n` for the fibre product of $[n]$ and $e$, with first projection $\iota \colon A[n] \to A$. Let $Z$ be an arbitrary subset of the underlying space of $A$ and $W$ an open subscheme of $A[n]$ whose underlying set is $\iota^{-1}(Z)$ (no openness of $Z$ itself is assumed). Then, for every $t \colon T \to \operatorname{Spec} R$ and every $T$-point $P$ of $A$ over $t$, the point $P$ factors through the inclusion $W \hookrightarrow A[n]$ followed by $\iota$ — that is, there is a morphism $P_0 \colon T \to W$ with $P_0$ followed by that composite equal to the underlying morphism of $P$ — if and only if the $n$-th multiple `nsmulPt L t n P` of $P$ (defined by the recursion $0 \mapsto L.one\,t$, $n+1 \mapsto L.mul\,t\,(\text{$n$-th multiple})\,P$) equals the unit point $L.one\,t$, and the set-theoretic image of the base map of $P$ is contained in $Z$.
--
--   This is the $T$-point description of an open piece of the $n$-torsion kernel scheme of a relative group law: membership in $W$ is exactly the conjunction of an $n$-torsion condition on $T$-points and a topological condition on the image. It is used when cutting out level structures and stabiliser conditions on torsion, being cited in the treatment of polarisations with two-torsion kernel and in the computation of the points of a level piece of a bare deformation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) (Z : Set ↥A)
    (W : (L.schemeKer n).Opens)
    (hW : (W : Set ↥(L.schemeKer n))
      = (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1).base ⁻¹' Z)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    FactorsThrough (W.ι ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) P ↔
      nsmulPt L t n P = L.one t ∧ Set.range P.1.base ⊆ Z := by sorry
